## ATLP 2023 - Refinement types

### Syntax

The first Lambda language as described in the notes

### Building and running

Assuming opam is installed along with the required libraries:

```
opam install pprint
opam install ppx_inline_test
```

Build and run the code using

```
dune build
dune exec -- ./bin/compiler.exe
```

### Testing

```
dune test
```

### Code formatting

Assuming `ocamlformat` is installed run

```
dune fmt
```
