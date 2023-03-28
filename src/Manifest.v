(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import Term_Defs_Core Maps.


Definition AM_Address : Set.
Admitted.

Definition ASP_Address : Set.
Admitted.

Definition PublicKey : Set.
Admitted.

Definition PolicyT : Set.
Admitted.

(*
Definition PlcMap := MapC Plc Address.
*)


(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
  Record Manifest := {

    local_asps : list ASP_ID ;
    server_asps : list ASP_ID ;
    knowsOf : list Plc ;
    pubkeys : list Plc ;
    policy : PolicyT
    (* TO DO: Add privacy and selection policies to manifest? *)
                    }.

(** Representation of a system's environment/resources used to populate a 
    ConcreteManifest based on an abstract Manifest. *)
  Record SystemConfig := {
    AM_Addresses : list AM_Address ;
    ASP_Addresses : list ASP_Address ;
                        }.
                           



  
 (* A ConcreteManifest is a refinement of Manifest with concrete parameters
    more suitable for extraction and deployment.  *)
  Record ConcreteManifest := {
        ASP_Server : ASP_Address ;
        Pubkey_Server : ASP_Address;
        Plc_Map : MapC Plc AM_Address;
        Pubkey_Map : MapC Plc PublicKey
                            }.



  (* This is a rough type signature for the "manifest compiler".  Still some details to be ironed out... *)
  Definition manifest_compiler : Manifest -> SystemConfig -> ConcreteManifest.
  Admitted.
