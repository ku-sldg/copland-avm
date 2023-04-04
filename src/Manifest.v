(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import Term_Defs_Core Maps Term_Defs.


Definition ASP_Address : Set. Admitted.

Definition UUID : Type. Admitted.

Definition PublicKey : Set. Admitted.

Definition PolicyT : Set. Admitted.

Definition CakeML_ASPCallback : Type := 
  ASP_PARAMS -> Plc -> BS -> RawEv -> BS.

Definition CakeML_PubKeyCallback : Type := 
  Plc -> PublicKey.

Definition CakeML_PlcCallback : Type := 
  Plc -> UUID.

(*
Definition PlcMap := MapC Plc Address.
*)


(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
  Record Manifest := {

    asps : list ASP_ID ;
    (* server_asps : list ASP_ID ; *)
    knowsOf : list Plc ;
    pubkeys : list PublicKey ;
    policy : PolicyT
    (* TO DO: Add privacy and selection policies to manifest? *)
  }.

(** Representation of a system's environment/resources used to populate a 
    ConcreteManifest based on an abstract Manifest. *)
  Record AM_Library := {
    Local_ASPS          : MapC ASP_ID CakeML_ASPCallback ;
    Local_Plcs          : MapC Plc UUID ;
    Local_PubKeys       : MapC Plc PublicKey ;
    Lib_ASP_Server      : (ASP_Address * CakeML_ASPCallback) ;
    Lib_PubKey_Server   : (ASP_Address * CakeML_PubKeyCallback) ;
    Lib_Plc_Server      : (ASP_Address * CakeML_PlcCallback) ;
  }.

  
 (* A ConcreteManifest is a refinement of Manifest with concrete parameters
    more suitable for extraction and deployment.  *)
  Record ConcreteManifest := {
    concrete_asps   : list ASP_ID ;
    concrete_plcs   : list Plc ;
    concrete_pubkeys: list PublicKey ;

    ASP_Server      : ASP_Address ;
    PubKey_Server   : ASP_Address ;
    Plc_Server      : ASP_Address ;
  }.

  Definition generate_ASP_dispatcher (al : AM_Library)
    : CakeML_ASPCallback.
  (* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
  destruct al. (* break up the library *) 
  (* Check is our parameter we are being called on is a local asp *)
  intros par.
  destruct par eqn:PAR. 
  (* our function is being called on asp with id "a" *)
  destruct (map_get Local_ASPS0 a).
  - (* if it is local, use the local callback *)
    eapply (c par).
  - (* it is not local, so dispatch to server *)
    destruct Lib_ASP_Server0.
    eapply (c par).
  Defined.

  Definition generate_Plc_dispatcher (al : AM_Library) 
    : CakeML_PlcCallback.
  destruct al.
  intros plc.
  destruct (map_get Local_Plcs0 plc).
  - eapply u.
  - destruct Lib_Plc_Server0.
    eapply (c plc).
  Defined.

  Definition generate_PubKey_dispatcher (al : AM_Library) 
    : CakeML_PubKeyCallback.
  destruct al.
  intros plc.
  destruct (map_get Local_PubKeys0 plc).
  - eapply p.
  - destruct Lib_PubKey_Server0.
    eapply (c plc).
  Defined.

  (* This is a rough type signature for the "manifest compiler".  Still some details to be ironed out... *)
  Definition manifest_compiler (m : Manifest) (al : AM_Library) 
    : (ConcreteManifest * CakeML_ASPCallback * 
      CakeML_PlcCallback * CakeML_PubKeyCallback).
  (* The output of this function is a Concrete manifest, and a 
  function that can be used like "check_asp_EXTD".
  This function will be used in extraction to either dispatch ASPs to the ASP server, or call a local callback *)
  pose proof (generate_ASP_dispatcher al).
  pose proof (generate_Plc_dispatcher al).
  pose proof (generate_PubKey_dispatcher al).
  split; [split; [split |]|]; eauto.
  eapply (Build_ConcreteManifest 
    m.(asps) m.(knowsOf) m.(pubkeys)
    (fst (al.(Lib_ASP_Server))) (fst (al.(Lib_Plc_Server)))
    (fst (al.(Lib_PubKey_Server)))).
  Defined.

