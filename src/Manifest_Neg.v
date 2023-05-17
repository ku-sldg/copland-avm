(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import Term_Defs_Core Copland_AC.

Require Import List.
Import List.ListNotations.


Definition PolicyT : Type.
Admitted.


(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its
   * interconnections).
   *)
  Record Manifest : Type := mk_manifest {

      asps : list ASP_ID ; 
      knowsOf : list Plc ; 
      pubkeys : list Plc ;
      (* policy : PolicyT *)
      (* context : list Plc ;  *)
      policy : ASP_ID -> Plc -> bool ;
      ac_policy : AC_Policy (* Permission -> Object -> bool  *)
                    }. 

   Definition empty_Manifest : Manifest :=
      mk_manifest [] [] [] (fun x y => false) (fun x y => false).

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
