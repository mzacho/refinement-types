## ATPLT 2023 - Refinement types

### Quickstart

Enter a nix-shell:

```
nix-shell
```

Print help:

```
make help
```

### Setup
Install the required libraries with opam:
```
opam pin add -y -n .
opam install --deps-only atplt2023
```

### Building and running

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
