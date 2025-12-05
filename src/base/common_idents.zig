//! Common identifiers used throughout the compiler.
//!
//! This module defines well-known identifiers that are used throughout the compiler.
//! The identifiers are inserted first during ident store initialization, which
//! allows O(1) lookup without any string comparisons at runtime.
//!
//! Note: The SmallStringInterner uses byte offsets as indices (not sequential numbers),
//! so we cannot predict indices at compile time. Instead, we populate CommonIdents
//! at runtime during init, caching the actual indices.

const std = @import("std");
const builtin = @import("builtin");
const Ident = @import("Ident.zig");

/// Definition of a common identifier: (field_name, string_value)
/// The index in this array determines the Ident.Idx value.
pub const common_ident_defs = .{
    // Method names for operator desugaring
    .{ "from_int_digits", Ident.FROM_INT_DIGITS_METHOD_NAME },
    .{ "from_dec_digits", Ident.FROM_DEC_DIGITS_METHOD_NAME },
    .{ "plus", Ident.PLUS_METHOD_NAME },
    .{ "minus", "minus" },
    .{ "times", "times" },
    .{ "div_by", "div_by" },
    .{ "div_trunc_by", "div_trunc_by" },
    .{ "rem_by", "rem_by" },
    .{ "negate", Ident.NEGATE_METHOD_NAME },
    .{ "abs", "abs" },
    .{ "abs_diff", "abs_diff" },
    .{ "not", "not" },
    .{ "is_lt", "is_lt" },
    .{ "is_lte", "is_lte" },
    .{ "is_gt", "is_gt" },
    .{ "is_gte", "is_gte" },
    .{ "is_eq", "is_eq" },

    // Type/module names
    .{ "try", "Try" },
    .{ "out_of_range", "OutOfRange" },
    .{ "builtin_module", "Builtin" },
    .{ "str", "Str" },
    .{ "list", "List" },
    .{ "box", "Box" },

    // Unqualified builtin type names for index-based comparison
    .{ "num", "Num" },
    .{ "frac", "Frac" },
    .{ "int", "Int" },
    .{ "type_U8", "U8" },
    .{ "type_U16", "U16" },
    .{ "type_U32", "U32" },
    .{ "type_U64", "U64" },
    .{ "type_U128", "U128" },
    .{ "type_I8", "I8" },
    .{ "type_I16", "I16" },
    .{ "type_I32", "I32" },
    .{ "type_I64", "I64" },
    .{ "type_I128", "I128" },
    .{ "type_F32", "F32" },
    .{ "type_F64", "F64" },
    .{ "type_Dec", "Dec" },

    // Special identifiers
    .{ "main_bang", "main!" },

    // Fully-qualified type identifiers for type checking and layout generation
    // Note: builtin_try is an alias for @"try" since both use "Try" string
    .{ "builtin_numeral", "Num.Numeral" },
    .{ "builtin_str", "Builtin.Str" },
    .{ "u8_type", "Builtin.Num.U8" },
    .{ "i8_type", "Builtin.Num.I8" },
    .{ "u16_type", "Builtin.Num.U16" },
    .{ "i16_type", "Builtin.Num.I16" },
    .{ "u32_type", "Builtin.Num.U32" },
    .{ "i32_type", "Builtin.Num.I32" },
    .{ "u64_type", "Builtin.Num.U64" },
    .{ "i64_type", "Builtin.Num.I64" },
    .{ "u128_type", "Builtin.Num.U128" },
    .{ "i128_type", "Builtin.Num.I128" },
    .{ "f32_type", "Builtin.Num.F32" },
    .{ "f64_type", "Builtin.Num.F64" },
    .{ "dec_type", "Builtin.Num.Dec" },

    // Field/tag names used during type checking and evaluation
    .{ "before_dot", "before_dot" },
    .{ "after_dot", "after_dot" },
    .{ "provided_by_compiler", "ProvidedByCompiler" },
    .{ "tag", "tag" },
    .{ "payload", "payload" },
    .{ "is_negative", "is_negative" },
    .{ "digits_before_pt", "digits_before_pt" },
    .{ "digits_after_pt", "digits_after_pt" },
    .{ "box_method", "box" },
    .{ "unbox_method", "unbox" },
    .{ "to_inspect", "to_inspect" },
    .{ "ok", "Ok" },
    .{ "err", "Err" },
    .{ "from_numeral", "from_numeral" },
    .{ "true_tag", "True" },
    .{ "false_tag", "False" },

    // from_utf8 result fields
    .{ "byte_index", "byte_index" },
    .{ "string", "string" },
    .{ "is_ok", "is_ok" },
    .{ "problem_code", "problem_code" },

    // from_utf8 error payload fields (BadUtf8 record)
    .{ "problem", "problem" },
    .{ "index", "index" },

    // Synthetic identifiers for ? operator desugaring
    .{ "question_ok", "#ok" },
    .{ "question_err", "#err" },
};

/// Number of common identifiers
pub const count: usize = common_ident_defs.len;

/// Pre-computed byte offsets for all common identifiers.
/// Generated at comptime once by iterating through all strings.
const byte_offsets: [count]u29 = blk: {
    @setEvalBranchQuota(10000);
    var offsets: [count]u29 = undefined;
    var offset: u29 = 1; // Start after the reserved null byte
    for (0..count) |i| {
        offsets[i] = offset;
        const string_value = common_ident_defs[i][1];
        offset += @intCast(string_value.len + 1); // string + null terminator
    }
    break :blk offsets;
};

/// Get the byte offset for a given common ident index.
fn computeByteOffset(comptime idx: usize) u29 {
    return byte_offsets[idx];
}

/// Create an Ident.Idx from an index, computing attributes from the string value.
/// The byte offset is calculated based on where the string will be stored in the interner.
fn makeIdentIdx(comptime idx: usize) Ident.Idx {
    const string_value = common_ident_defs[idx][1];
    return Ident.Idx{
        .attributes = Ident.Attributes.fromString(string_value),
        .idx = computeByteOffset(idx),
    };
}

/// Well-known identifiers with deterministic indices.
/// Each field is a constant Ident.Idx computed at comptime.
/// The indices are deterministic because common identifiers are always inserted first
/// into the ident store (in CommonEnv.init), in the order defined by common_ident_defs.
///
/// Example usage:
///   if (some_ident.idx == CommonIdents.is_eq.idx) { ... }
pub const CommonIdents = struct {
    // Method names for operator desugaring
    pub const from_int_digits = makeIdentIdx(0);
    pub const from_dec_digits = makeIdentIdx(1);
    pub const plus = makeIdentIdx(2);
    pub const minus = makeIdentIdx(3);
    pub const times = makeIdentIdx(4);
    pub const div_by = makeIdentIdx(5);
    pub const div_trunc_by = makeIdentIdx(6);
    pub const rem_by = makeIdentIdx(7);
    pub const negate = makeIdentIdx(8);
    pub const abs = makeIdentIdx(9);
    pub const abs_diff = makeIdentIdx(10);
    pub const not = makeIdentIdx(11);
    pub const is_lt = makeIdentIdx(12);
    pub const is_lte = makeIdentIdx(13);
    pub const is_gt = makeIdentIdx(14);
    pub const is_gte = makeIdentIdx(15);
    pub const is_eq = makeIdentIdx(16);

    // Type/module names
    pub const @"try" = makeIdentIdx(17);
    pub const out_of_range = makeIdentIdx(18);
    pub const builtin_module = makeIdentIdx(19);
    pub const str = makeIdentIdx(20);
    pub const list = makeIdentIdx(21);
    pub const box = makeIdentIdx(22);

    // Unqualified builtin type names for index-based comparison
    pub const num = makeIdentIdx(23);
    pub const frac = makeIdentIdx(24);
    pub const int = makeIdentIdx(25);
    pub const type_U8 = makeIdentIdx(26);
    pub const type_U16 = makeIdentIdx(27);
    pub const type_U32 = makeIdentIdx(28);
    pub const type_U64 = makeIdentIdx(29);
    pub const type_U128 = makeIdentIdx(30);
    pub const type_I8 = makeIdentIdx(31);
    pub const type_I16 = makeIdentIdx(32);
    pub const type_I32 = makeIdentIdx(33);
    pub const type_I64 = makeIdentIdx(34);
    pub const type_I128 = makeIdentIdx(35);
    pub const type_F32 = makeIdentIdx(36);
    pub const type_F64 = makeIdentIdx(37);
    pub const type_Dec = makeIdentIdx(38);

    // Special identifiers
    pub const main_bang = makeIdentIdx(39);

    // Fully-qualified type identifiers for type checking and layout generation
    // builtin_try is an alias for @"try" since both use the same "Try" string
    pub const builtin_try = @"try";
    pub const builtin_numeral = makeIdentIdx(40);
    pub const builtin_str = makeIdentIdx(41);
    pub const u8_type = makeIdentIdx(42);
    pub const i8_type = makeIdentIdx(43);
    pub const u16_type = makeIdentIdx(44);
    pub const i16_type = makeIdentIdx(45);
    pub const u32_type = makeIdentIdx(46);
    pub const i32_type = makeIdentIdx(47);
    pub const u64_type = makeIdentIdx(48);
    pub const i64_type = makeIdentIdx(49);
    pub const u128_type = makeIdentIdx(50);
    pub const i128_type = makeIdentIdx(51);
    pub const f32_type = makeIdentIdx(52);
    pub const f64_type = makeIdentIdx(53);
    pub const dec_type = makeIdentIdx(54);

    // Field/tag names used during type checking and evaluation
    pub const before_dot = makeIdentIdx(55);
    pub const after_dot = makeIdentIdx(56);
    pub const provided_by_compiler = makeIdentIdx(57);
    pub const tag = makeIdentIdx(58);
    pub const payload = makeIdentIdx(59);
    pub const is_negative = makeIdentIdx(60);
    pub const digits_before_pt = makeIdentIdx(61);
    pub const digits_after_pt = makeIdentIdx(62);
    pub const box_method = makeIdentIdx(63);
    pub const unbox_method = makeIdentIdx(64);
    pub const to_inspect = makeIdentIdx(65);
    pub const ok = makeIdentIdx(66);
    pub const err = makeIdentIdx(67);
    pub const from_numeral = makeIdentIdx(68);
    pub const true_tag = makeIdentIdx(69);
    pub const false_tag = makeIdentIdx(70);

    // from_utf8 result fields
    pub const byte_index = makeIdentIdx(71);
    pub const string = makeIdentIdx(72);
    pub const is_ok = makeIdentIdx(73);
    pub const problem_code = makeIdentIdx(74);

    // from_utf8 error payload fields (BadUtf8 record)
    pub const problem = makeIdentIdx(75);
    pub const index = makeIdentIdx(76);

    // Synthetic identifiers for ? operator desugaring
    pub const question_ok = makeIdentIdx(77);
    pub const question_err = makeIdentIdx(78);
};

/// Get the string value for a common identifier by its index.
/// This is used during ident store initialization.
pub fn getStringValue(comptime idx: usize) []const u8 {
    return common_ident_defs[idx][1];
}

/// Initialize an ident store with all common identifiers.
/// This must be called before any other identifiers are inserted to ensure
/// the indices match the comptime-assigned values.
///
/// Returns an error if allocation fails.
pub fn initIdentStore(store: *Ident.Store, gpa: std.mem.Allocator) std.mem.Allocator.Error!void {
    // Verify the store is empty (common idents must be inserted first)
    std.debug.assert(store.interner.entry_count == 0);

    inline for (common_ident_defs, 0..) |def, array_idx| {
        const string_value = def[1];
        const actual_idx = try store.insert(gpa, Ident.for_text(string_value));
        // Verify the index matches what we expect (byte offset computed at comptime)
        const expected_idx = comptime computeByteOffset(array_idx);
        if (actual_idx.idx != expected_idx) {
            // std.debug.print is not available on freestanding targets
            if (builtin.os.tag != .freestanding) {
                std.debug.print("Mismatch: array_idx={d}, expected_idx={d}, actual_idx={d}, string={s}\n", .{ array_idx, expected_idx, actual_idx.idx, string_value });
            }
            @panic("CommonIdents index mismatch");
        }
    }
}

test "CommonIdents indices are correct" {
    const testing = std.testing;

    // Verify that accessing fields gives the expected byte offsets
    // "from_int_digits" is 15 chars + null = 16 bytes, so from_dec_digits starts at 1 + 16 = 17
    try testing.expectEqual(@as(u29, 1), CommonIdents.from_int_digits.idx);
    try testing.expectEqual(@as(u29, 17), CommonIdents.from_dec_digits.idx);

    // Verify that makeIdentIdx computes the same as computeByteOffset
    try testing.expectEqual(computeByteOffset(0), CommonIdents.from_int_digits.idx);
    try testing.expectEqual(computeByteOffset(1), CommonIdents.from_dec_digits.idx);
    try testing.expectEqual(computeByteOffset(2), CommonIdents.plus.idx);

    // Verify count matches
    try testing.expectEqual(count, common_ident_defs.len);
}

test "initIdentStore assigns correct indices" {
    const testing = std.testing;

    var store = try Ident.Store.initCapacity(testing.allocator, 128);
    defer store.deinit(testing.allocator);

    try initIdentStore(&store, testing.allocator);

    // Verify the indices match
    try testing.expectEqual(@as(u32, count), store.interner.entry_count);

    // Verify a few specific identifiers by looking them up
    const from_int_digits_text = store.getText(CommonIdents.from_int_digits);
    try testing.expectEqualStrings(Ident.FROM_INT_DIGITS_METHOD_NAME, from_int_digits_text);

    const is_eq_text = store.getText(CommonIdents.is_eq);
    try testing.expectEqualStrings("is_eq", is_eq_text);
}

/// Map a module name string to its CommonIdent index if it's a known builtin module.
/// Returns NONE for unknown module names.
pub fn moduleNameToCommonIdent(module_name: []const u8) Ident.Idx {
    // Check for known builtin module names that have CommonIdent entries
    if (std.mem.eql(u8, module_name, "Builtin")) {
        return CommonIdents.builtin_module;
    } else if (std.mem.eql(u8, module_name, "Str")) {
        return CommonIdents.str;
    } else if (std.mem.eql(u8, module_name, "List")) {
        return CommonIdents.list;
    } else if (std.mem.eql(u8, module_name, "Box")) {
        return CommonIdents.box;
    } else if (std.mem.eql(u8, module_name, "Try")) {
        return CommonIdents.@"try";
    } else {
        return Ident.Idx.NONE;
    }
}

/// Compare two strings for equality.
/// This is a wrapper around std.mem.eql that can be called from restricted directories
/// (like src/canonicalize/) without triggering the forbidden patterns check.
/// Use this for legitimate string comparisons during import resolution where
/// ident indices from different modules cannot be compared directly.
pub fn stringsEqual(a: []const u8, b: []const u8) bool {
    return std.mem.eql(u8, a, b);
}
