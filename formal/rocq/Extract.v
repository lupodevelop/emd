(* Extracts the Rocq model to OCaml so tests can run it. Z stays inductive: no
   mapping to machine integers, so extraction adds no arithmetic of its own. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From EmdFormal Require Import Emd.

Extraction Language OCaml.
Extraction "emd_extracted.ml" decode_source run init.
