(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import Term_Defs_Core Copland_AC.


(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its
   * interconnections).
   *)
  Record Manifest := {

      asps : list ASP_ID ;
      knowsOf : list Plc ; 
      context : list Plc ; 
      policy : ASP_ID -> Plc -> bool ;
      ac_policy : AC_Policy (* Permission -> Object -> bool  *)
                    }.

 (* A ConcreteManifest is a refinement of Manifest with concrete parameters
    more suitable for extraction and deployment 
  *)
  Record ConcreteManifest := {

(*
      ; C : list string
      ; key : string
      ; address : nat
      ; tpm_init : nat
*)
    }.
