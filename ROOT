(* An Isabelle session is a build target. This one extends the standard HOL
   session and starts from Benchmark, which imports the other project theories. *)
session Bridge_Benchmark = HOL +
(* Skip rendering a document and require checked proofs. The sessions stanza
   lists the extra library used for code generation. *)
  options [document = false, quick_and_dirty = false]
  sessions
    "HOL-Library"
  theories
    Benchmark
