(lang dune 3.0)

(name refinement_types)

(generate_opam_files true)

(using menhir 2.1)

(package
 (name refinement_types)
 (synopsis "Refinement type system")
 (depends ocaml dune ppx_inline_test bisect_ppx pprint ocamlformat z3)
)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
