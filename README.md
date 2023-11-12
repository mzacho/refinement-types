## ATPLT 2023 - Refinement types

### Syntax

The first Lambda language as described in the notes

### Building and running

Assuming opam is installed along with the required libraries:

```
opam pin add -y -n .
opam install --deps-only atplt2023
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

Correct formatting can be ensured using a `pre-commit` hook.
Install using `pip install pre-commit`, then in the repo: `pre-commit install`.
