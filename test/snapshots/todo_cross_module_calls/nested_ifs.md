# META
~~~ini
description=Nested if expressions
type=repl
~~~
# SOURCE
~~~roc
» if True (if False 1 else 2) else 3
» if False 1 else (if True 2 else 3)
~~~
# OUTPUT
2
---
2
# PROBLEMS
NIL
