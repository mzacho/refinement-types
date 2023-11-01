## ATLP 2023 - Refinement types

### Syntax

Expressions:
```
e ::= x
    | e e
    | (fn (params) e)

params ::= ɛ | x:t, params
```

Types:
```
t ::= x
    | t -> t
```

Variable names:
```
x ::= 0 | 1 | 2 | ...
```

### Building and running

```
dune build
dune exec -- ./bin/compiler.exe
```
