(lang dune 3.23)
(using rocq 0.13)
(name OneNumType)

(generate_opam_files true)

(source
 (github ybertot/one_num_type))

(authors "Thomas Portet  <Thomas.Porter@inria.fr>"
  "Yves Bertot <Yves.Bertot@inria.fr>")

(maintainers "Yves Bertot <Yves.Bertot@inria.fr>")

(license MIT)

(documentation https://url/to/documentation)

(package
 (name OneNum)
 (synopsis "Ext")
 (description "Ext")
 (depends rocq-elpi))

(package
 (name rocq-elpi-ext-tests)
 (allow_empty)
 (synopsis "Ext")
 (description "Ext")
 (depends rocq-elpi))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
