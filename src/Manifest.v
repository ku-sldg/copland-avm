(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import Term_Defs_Core.


(** [Manifest] defines an attestation manger a list of ASPs and other
   * managers it is aware of.  [Manifest] defines a single AM and its
   * interconnections.  [add] simulates address information and [tpm]
   * simulates cruft necessary to initialize its TPM.
   *)
  Record Manifest := {

      asps : list ASP_ID ;
      knowsOf : list Plc ; 
      (* previously M*)

(*
      ; C : list string
      ; key : string
      ; address : nat
      ; tpm_init : nat
*)

(* TO DO: Add privacy and selection policies to manifest *)
    }.
