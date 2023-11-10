(lang dune 3.0)

(name atplt2023)

(generate_opam_files true)

(package
 (name atplt2023)
 (synopsis "Refinement type system")
 (depends ocaml dune ppx_inline_test bisect_ppx pprint ocamlformat z3)
)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
