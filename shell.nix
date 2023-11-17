{ nixpkgs ? import <nixpkgs> { }}:

let
  pinnedPkgs = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/23.05.tar.gz";
    sha256 = "10wn0l08j9lgqcw8177nh2ljrnxdrpri7bp0g7nvrsn9rkawvlbf";
  };
  pkgs = import pinnedPkgs {};
in

pkgs.mkShell {
  buildInputs = with pkgs; [
    # General
    python311
    z3

    # Ocaml
    ocamlPackages.ocaml
    ocamlPackages.dune_3
    ocamlPackages.findlib
    ocamlPackages.bisect_ppx
    ocamlPackages.ppxlib
    ocamlPackages.ppx_inline_test
    ocamlPackages.pprint
    ocamlPackages.z3
  ];
}
