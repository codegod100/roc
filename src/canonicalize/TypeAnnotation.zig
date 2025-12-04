//! Representation of type annotations in the Canonical Intermediate Representation (CIR).
//!
//! Includes formatting of type annotations to s-expression debug format.

const std = @import("std");
const base = @import("base");
const types = @import("types");
const builtins = @import("builtins");
const collections = @import("collections");

const ModuleEnv = @import("ModuleEnv.zig");
const CIR = @import("CIR.zig");
const Diagnostic = @import("Diagnostic.zig");
const Region = base.Region;
const StringLiteral = base.StringLiteral;
const Ident = base.Ident;
const DataSpan = base.DataSpan;
const SExpr = base.SExpr;
const SExprTree = base.SExprTree;
const TypeVar = types.Var;
const Expr = CIR.Expr;
const Statement = CIR.Statement;
const IntValue = CIR.IntValue;
const RocDec = builtins.RocDec;

/// Canonical representation of type annotations in Roc.
///
/// Type annotations appear on the right-hand side of type declarations and in other
/// contexts where types are specified. For example, in `Map(a, b) : List(a) -> List(b)`,
/// the `List(a) -> List(b)` part is represented by these TypeAnno variants.
pub const TypeAnno = union(enum) {
    /// Type application: applying a type constructor to arguments.
    ///
    /// Examples: `List(Str)`, `Dict(String, Int)`, `Result(a, b)`
    apply: Apply,
    /// Type variable: a placeholder type that can be unified with other types.
    ///
    /// Examples: `a`, `b`, `elem` in generic type signatures
    rigid_var: struct {
        name: Ident.Idx, // The variable name (e.g., "a", "b")
    },
    /// A rigid var that references another
    ///
    /// Examples:
    ///
    ///   MyAlias(a) = List(a)
    /// rigid_var ^         ^ rigid_var_lookup
    ///
    /// myFunction : a -> a
    ///    rigid_var ^    ^ rigid_var_lookup
    rigid_var_lookup: struct {
        ref: TypeAnno.Idx, // The variable name (e.g., "a", "b")
    },
    /// Inferred type `_`
    underscore: void,
    /// Basic type identifier: a concrete type name without arguments.
    ///
    /// Examples: `Str`, `U64`, `Bool`
    lookup: struct {
        name: Ident.Idx, // The type name
        base: LocalOrExternal,
    },
    /// Tag union type: a union of tags, possibly with payloads.
    ///
    /// Examples: `[Some(a), None]`, `[Red, Green, Blue]`, `[Cons(a, (List a)), Nil]`
    tag_union: TagUnion,
    /// A tag in a gat union
    ///
    /// Examples: `Some(a)`, `None`
    tag: struct {
        name: Ident.Idx, // The tag name
        args: TypeAnno.Span, // The tag arguments
    },
    /// Tuple type: a fixed-size collection of heterogeneous types.
    ///
    /// Examples: `(Str, U64)`, `(a, b, c)`
    tuple: Tuple,
    /// Record type: a collection of named fields with their types.
    ///
    /// Examples: `{ name: Str, age: U64 }`, `{ x: F64, y: F64 }`
    record: Record,
    /// Function type: represents function signatures.
    ///
    /// Examples: `a -> b`, `Str, U64 -> Str`, `{} => Str`
    @"fn": Func,
    /// Parenthesized type: used for grouping and precedence.
    ///
    /// Examples: `(a -> b)` in `a, (a -> b) -> b`
    parens: struct {
        anno: TypeAnno.Idx, // The type inside the parentheses
    },
    /// Malformed type annotation: represents a type that couldn't be parsed correctly.
    /// This follows the "Inform Don't Block" principle - compilation continues with
    /// an error marker that will be reported to the user.
    malformed: struct {
        diagnostic: CIR.Diagnostic.Idx, // The error that occurred
    },

    pub const Idx = enum(u32) { _ };
    pub const Span = extern struct { span: DataSpan };

    pub fn pushToSExprTree(self: *const @This(), ir: *const ModuleEnv, tree: *SExprTree, type_anno_idx: TypeAnno.Idx) std.mem.Allocator.Error!void {
        switch (self.*) {
            .apply => |a| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-apply");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                try tree.pushStringPair("name", ir.getIdentText(a.name));

                switch (a.base) {
                    .builtin => |_| {
                        const field_begin = tree.beginNode();
                        try tree.pushStaticAtom("builtin");
                        const field_attrs = tree.beginNode();
                        try tree.endNode(field_begin, field_attrs);
                    },
                    .local => |_| {
                        const field_begin = tree.beginNode();
                        try tree.pushStaticAtom("local");
                        const field_attrs = tree.beginNode();
                        try tree.endNode(field_begin, field_attrs);
                    },
                    .external => |external| {
                        // Special case: Builtin module is an implementation detail, print as (builtin)
                        // Use index comparison instead of string comparison
                        const is_builtin = if (ir.imports.getIdentIdx(external.module_idx)) |ident|
                            ident.idx == ir.idents.builtin_module.idx
                        else
                            false;

                        if (is_builtin) {
                            const field_begin = tree.beginNode();
                            try tree.pushStaticAtom("builtin");
                            const field_attrs = tree.beginNode();
                            try tree.endNode(field_begin, field_attrs);
                        } else {
                            const module_idx_int = @intFromEnum(external.module_idx);
                            std.debug.assert(module_idx_int < ir.imports.imports.items.items.len);
                            const string_lit_idx = ir.imports.imports.items.items[module_idx_int];
                            const module_name = ir.common.strings.get(string_lit_idx);
                            try tree.pushStringPair("external-module", module_name);
                        }
                    },
                }

                const attrs = tree.beginNode();
                const args_slice = ir.store.sliceTypeAnnos(a.args);
                for (args_slice) |arg_idx| {
                    try ir.store.getTypeAnno(arg_idx).pushToSExprTree(ir, tree, arg_idx);
                }

                try tree.endNode(begin, attrs);
            },
            .rigid_var => |tv| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-rigid-var");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                try tree.pushStringPair("name", ir.getIdentText(tv.name));
                const attrs = tree.beginNode();
                try tree.endNode(begin, attrs);
            },
            .rigid_var_lookup => |rv_lookup| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-rigid-var-lookup");
                try ir.store.getTypeAnno(rv_lookup.ref).pushToSExprTree(ir, tree, rv_lookup.ref);
                const attrs = tree.beginNode();
                try tree.endNode(begin, attrs);
            },
            .underscore => |_| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-underscore");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                const attrs = tree.beginNode();
                try tree.endNode(begin, attrs);
            },
            .lookup => |t| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-lookup");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                try tree.pushStringPair("name", ir.getIdentText(t.name));

                switch (t.base) {
                    .builtin => |_| {
                        const field_begin = tree.beginNode();
                        try tree.pushStaticAtom("builtin");
                        const field_attrs = tree.beginNode();
                        try tree.endNode(field_begin, field_attrs);
                    },
                    .local => |_| {
                        const field_begin = tree.beginNode();
                        try tree.pushStaticAtom("local");
                        const field_attrs = tree.beginNode();
                        try tree.endNode(field_begin, field_attrs);
                    },
                    .external => |external| {
                        // Special case: Builtin module is an implementation detail, print as (builtin)
                        // Use index comparison instead of string comparison
                        const is_builtin = if (ir.imports.getIdentIdx(external.module_idx)) |ident|
                            ident.idx == ir.idents.builtin_module.idx
                        else
                            false;

                        if (is_builtin) {
                            const field_begin = tree.beginNode();
                            try tree.pushStaticAtom("builtin");
                            const field_attrs = tree.beginNode();
                            try tree.endNode(field_begin, field_attrs);
                        } else {
                            const module_idx_int = @intFromEnum(external.module_idx);
                            std.debug.assert(module_idx_int < ir.imports.imports.items.items.len);
                            const string_lit_idx = ir.imports.imports.items.items[module_idx_int];
                            const module_name = ir.common.strings.get(string_lit_idx);
                            try tree.pushStringPair("external-module", module_name);
                        }
                    },
                }

                const attrs = tree.beginNode();
                try tree.endNode(begin, attrs);
            },
            .tag_union => |tu| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-tag-union");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                const attrs = tree.beginNode();

                const tags_slice = ir.store.sliceTypeAnnos(tu.tags);
                for (tags_slice) |tag_idx| {
                    try ir.store.getTypeAnno(tag_idx).pushToSExprTree(ir, tree, tag_idx);
                }

                if (tu.ext) |open_idx| {
                    try ir.store.getTypeAnno(open_idx).pushToSExprTree(ir, tree, open_idx);
                }

                try tree.endNode(begin, attrs);
            },
            .tag => |t| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-tag-name");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);

                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                try tree.pushStringPair("name", ir.getIdentText(t.name));

                const attrs = tree.beginNode();
                const args_slice = ir.store.sliceTypeAnnos(t.args);
                for (args_slice) |tag_idx| {
                    try ir.store.getTypeAnno(tag_idx).pushToSExprTree(ir, tree, tag_idx);
                }
                try tree.endNode(begin, attrs);
            },
            .tuple => |t| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-tuple");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                const attrs = tree.beginNode();

                const annos_slice = ir.store.sliceTypeAnnos(t.elems);
                for (annos_slice) |anno_idx| {
                    try ir.store.getTypeAnno(anno_idx).pushToSExprTree(ir, tree, anno_idx);
                }

                try tree.endNode(begin, attrs);
            },
            .record => |r| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-record");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                const attrs = tree.beginNode();

                const fields_slice = ir.store.sliceAnnoRecordFields(r.fields);
                for (fields_slice) |field_idx| {
                    const field = ir.store.getAnnoRecordField(field_idx);

                    const field_begin = tree.beginNode();
                    try tree.pushStaticAtom("field");
                    try tree.pushStringPair("field", ir.getIdentText(field.name));
                    const field_attrs = tree.beginNode();

                    try ir.store.getTypeAnno(field.ty).pushToSExprTree(ir, tree, field.ty);

                    try tree.endNode(field_begin, field_attrs);
                }

                try tree.endNode(begin, attrs);
            },
            .@"fn" => |f| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-fn");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                try tree.pushBoolPair("effectful", f.effectful);
                const attrs = tree.beginNode();

                const args_slice = ir.store.sliceTypeAnnos(f.args);
                for (args_slice) |arg_idx| {
                    try ir.store.getTypeAnno(arg_idx).pushToSExprTree(ir, tree, arg_idx);
                }

                try ir.store.getTypeAnno(f.ret).pushToSExprTree(ir, tree, f.ret);

                try tree.endNode(begin, attrs);
            },
            .parens => |p| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-parens");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                const attrs = tree.beginNode();

                try ir.store.getTypeAnno(p.anno).pushToSExprTree(ir, tree, p.anno);

                try tree.endNode(begin, attrs);
            },
            .malformed => |_| {
                const begin = tree.beginNode();
                try tree.pushStaticAtom("ty-malformed");
                const region = ir.store.getTypeAnnoRegion(type_anno_idx);
                try ir.appendRegionInfoToSExprTreeFromRegion(tree, region);
                const attrs = tree.beginNode();
                try tree.endNode(begin, attrs);
            },
        }
    }

    /// Record field in a type annotation: `{ field_name: Type }`
    pub const RecordField = struct {
        name: Ident.Idx,
        ty: TypeAnno.Idx,

        pub const Idx = enum(u32) { _ };
        pub const Span = extern struct { span: DataSpan };
    };

    /// Either a locally declare type, or an external type
    pub const LocalOrExternal = union(enum) {
        builtin: Builtin,
        local: struct {
            decl_idx: Statement.Idx,
        },
        external: struct {
            module_idx: CIR.Import.Idx,
            target_node_idx: u16,
        },

        // Just the tag of this union enum
        pub const Tag = std.meta.Tag(@This());
    };

    /// A type application in a type annotation
    pub const Apply = struct {
        name: Ident.Idx, // The type name
        base: LocalOrExternal, // Reference to the type
        args: TypeAnno.Span, // The type arguments (e.g., [Str], [String, Int])
    };

    /// A func in a type annotation
    pub const Func = struct {
        args: TypeAnno.Span, // Argument types
        ret: TypeAnno.Idx, // Return type
        effectful: bool, // Whether the function can perform effects, i.e. uses fat arrow `=>`
    };

    /// A record in a type annotation
    pub const Record = struct {
        fields: RecordField.Span, // The field definitions
    };

    /// A tag union in a type annotation
    pub const TagUnion = struct {
        tags: TypeAnno.Span, // The individual tags in the union
        ext: ?TypeAnno.Idx, // Optional extension variable for open unions
    };

    /// A tuple in a type annotation
    pub const Tuple = struct {
        elems: TypeAnno.Span, // The types of each tuple element
    };

    /// A builtin type
    pub const Builtin = enum {
        list,
        box,
        num,
        frac,
        int,
        u8,
        u16,
        u32,
        u64,
        u128,
        i8,
        i16,
        i32,
        i64,
        i128,
        f32,
        f64,
        dec,

        /// Convert a builtin type to it's name
        pub fn toBytes(self: @This()) []const u8 {
            switch (self) {
                .list => return "List",
                .box => return "Box",
                .num => return "Num",
                .frac => return "Frac",
                .int => return "Int",
                .u8 => return "U8",
                .u16 => return "U16",
                .u32 => return "U32",
                .u64 => return "U64",
                .u128 => return "U128",
                .i8 => return "I8",
                .i16 => return "I16",
                .i32 => return "I32",
                .i64 => return "I64",
                .i128 => return "I128",
                .f32 => return "F32",
                .f64 => return "F64",
                .dec => return "Dec",
            }
        }

        /// Convert a type name string to the corresponding builtin type.
        /// DEPRECATED: Use fromIdent instead for index-based comparison.
        pub fn fromBytes(bytes: []const u8) ?@This() {
            // Use character-based parsing to avoid string comparisons
            if (bytes.len == 0) return null;
            return switch (bytes[0]) {
                'L' => if (bytes.len == 4 and bytes[1] == 'i' and bytes[2] == 's' and bytes[3] == 't') .list else null,
                'B' => if (bytes.len == 3 and bytes[1] == 'o' and bytes[2] == 'x') .box else null,
                'N' => if (bytes.len == 3 and bytes[1] == 'u' and bytes[2] == 'm') .num else null,
                'F' => blk: {
                    if (bytes.len == 4 and bytes[1] == 'r' and bytes[2] == 'a' and bytes[3] == 'c') break :blk .frac;
                    if (bytes.len == 3 and bytes[1] == '3' and bytes[2] == '2') break :blk .f32;
                    if (bytes.len == 3 and bytes[1] == '6' and bytes[2] == '4') break :blk .f64;
                    break :blk null;
                },
                'I' => blk: {
                    if (bytes.len == 3 and bytes[1] == 'n' and bytes[2] == 't') break :blk .int;
                    if (bytes.len == 2 and bytes[1] == '8') break :blk .i8;
                    if (bytes.len == 3 and bytes[1] == '1' and bytes[2] == '6') break :blk .i16;
                    if (bytes.len == 3 and bytes[1] == '3' and bytes[2] == '2') break :blk .i32;
                    if (bytes.len == 3 and bytes[1] == '6' and bytes[2] == '4') break :blk .i64;
                    if (bytes.len == 4 and bytes[1] == '1' and bytes[2] == '2' and bytes[3] == '8') break :blk .i128;
                    break :blk null;
                },
                'U' => blk: {
                    if (bytes.len == 2 and bytes[1] == '8') break :blk .u8;
                    if (bytes.len == 3 and bytes[1] == '1' and bytes[2] == '6') break :blk .u16;
                    if (bytes.len == 3 and bytes[1] == '3' and bytes[2] == '2') break :blk .u32;
                    if (bytes.len == 3 and bytes[1] == '6' and bytes[2] == '4') break :blk .u64;
                    if (bytes.len == 4 and bytes[1] == '1' and bytes[2] == '2' and bytes[3] == '8') break :blk .u128;
                    break :blk null;
                },
                'D' => if (bytes.len == 3 and bytes[1] == 'e' and bytes[2] == 'c') .dec else null,
                else => null,
            };
        }

        /// Convert an identifier index to the corresponding builtin type.
        /// Uses index comparison for efficiency (no string comparison).
        pub fn fromIdent(ident: Ident.Idx, idents: *const ModuleEnv.CommonIdents) ?@This() {
            const idx = ident.idx;
            if (idx == idents.list.idx) return .list;
            if (idx == idents.box.idx) return .box;
            if (idx == idents.num.idx) return .num;
            if (idx == idents.frac.idx) return .frac;
            if (idx == idents.int.idx) return .int;
            if (idx == idents.type_U8.idx) return .u8;
            if (idx == idents.type_U16.idx) return .u16;
            if (idx == idents.type_U32.idx) return .u32;
            if (idx == idents.type_U64.idx) return .u64;
            if (idx == idents.type_U128.idx) return .u128;
            if (idx == idents.type_I8.idx) return .i8;
            if (idx == idents.type_I16.idx) return .i16;
            if (idx == idents.type_I32.idx) return .i32;
            if (idx == idents.type_I64.idx) return .i64;
            if (idx == idents.type_I128.idx) return .i128;
            if (idx == idents.type_F32.idx) return .f32;
            if (idx == idents.type_F64.idx) return .f64;
            if (idx == idents.type_Dec.idx) return .dec;
            return null;
        }
    };
};

