{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  packages = with pkgs; [
    ocaml
    dune_3
    ocamlformat
    ocamlPackages.utop
    ocamlPackages.findlib
    ocamlPackages.ocaml-lsp
    ocamlPackages.menhir
    # ocamlPackages.ocamlformat
    ocamlPackages.ppx_inline_test
    ocamlPackages.pprint
    ocamlPackages.bisect_ppx
    ocamlPackages.z3
    z3
    pre-commit
  ];
}
