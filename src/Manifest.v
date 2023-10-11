(* Adapted from:  
   https://github.com/ku-sldg/negotiation20/blob/master/src/Manifest/Manifest.v
*)

Require Import AbstractedTypes Term_Defs_Core Maps String
  Term_Defs Manifest_Admits EqClass ErrorStMonad_Coq.

Require Import Example_Phrases_Admits.

Require Import List.
Import ListNotations.

Inductive DispatcherErrors : Type :=
| Unavailable   : DispatcherErrors
| Runtime       : StringT -> DispatcherErrors.

Inductive CallBackErrors : Type := 
| messageLift   : StringT -> CallBackErrors.

Definition ASPCallback (ErrType : Type) : Type := 
  ASP_PARAMS -> Plc -> BS -> RawEv -> ResultT BS ErrType.

Definition PubKeyCallback : Type := 
  Plc -> ResultT PublicKey DispatcherErrors.

Definition PlcCallback : Type := 
  Plc -> ResultT UUID DispatcherErrors.

Definition UUIDCallback : Type :=
  UUID -> ResultT Plc DispatcherErrors.

(*
Definition PlcMap := MapC Plc Address.
*)


Definition PolicyT : Set :=  list (Plc * ASP_ID).

Definition empty_PolicyT : PolicyT := [].
  (* [(P0, attest_id)]. *)

Definition manifest_set (A:Type) : Set.
Admitted.

Definition manifest_set_empty {A:Type} : manifest_set A.
Admitted.

Definition manset_add{A:Type} (x:A) (s:manifest_set A) : manifest_set A.
Admitted.

Definition list_to_manset{A:Type} : list A -> manifest_set A.
Admitted.




(*
Check In.
In
	 : forall A : Type, A -> list A -> Prop
*)

(*
Check in_dec.
in_dec
	 : forall A : Type,
       (forall x y : A, {x = y} + {x <> y}) ->
       forall (a : A) (l : list A), {In a l} + {~ In a l}
*)

Definition In_set{A:Type} : A -> manifest_set A -> Prop.
Admitted.

Definition in_dec_set {A:Type} :
(forall x y : A, {x = y} + {x <> y}) ->
forall (a : A) (l : manifest_set A), {In_set a l} + {~ In_set a l}.
Admitted.

Lemma In_set_empty_contra{A:Type} : forall (i:A) (P:Prop),
  In_set i manifest_set_empty -> P.
Proof.
Admitted.

Lemma manadd_In_set{A:Type} : forall (s:manifest_set A) i j,
In_set i (manset_add j s) -> 
i = j \/ In_set i s.
Proof.
Admitted.

Lemma manadd_In_add{A:Type} : forall (s:manifest_set A) i,
In_set i (manset_add i s).
Proof.
Admitted.

Lemma in_set_add{A:Type} : forall (s:manifest_set A) i j,
In_set i s -> 
In_set i (manset_add j s).
Proof.
Admitted.

(*
Check existsb.

existsb
	 : forall A : Type, (A -> bool) -> list A -> bool
*)
Definition existsb_set{A:Type} : (A -> bool) -> manifest_set A -> bool.
Admitted.

(*
Check existsb_eq_iff_In
existsb_eq_iff_In
	 : forall (l : list ID_Type) (a : ID_Type),
       existsb (eqb a) l = true <-> In a l
*)
Definition existsb_eq_iff_In_set: forall (l : manifest_set ID_Type) (a : ID_Type),
existsb_set (eqb a) l = true <-> In_set a l.
Admitted.



(** [Manifest] defines an attestation manger, a list of ASPs, and other
   * managers it is aware of (a single AM and its interconnections).
   *)
  Record Manifest := {
    my_abstract_plc   : Plc ; 

    asps              : manifest_set ASP_ID; (* list ASP_ID ; *)
    appraisal_asps    : manifest_set (Plc * ASP_ID) ;
    uuidPlcs          : manifest_set Plc ;
    pubKeyPlcs        : manifest_set Plc ;
    targetPlcs        : manifest_set Plc ;
    policy            : PolicyT  ;
    (* TO DO: Add privacy and selection policies to manifest? *)
  }.

  Definition empty_Manifest : Manifest :=
    Build_Manifest 
      empty_Manifest_Plc 
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      manifest_set_empty
      empty_PolicyT.

(** Representation of a system's environment/resources used to populate an 
    AM Config based on a Manifest. *)
  Record AM_Library := {
    ASPServer_Cb        : ASP_Address -> (ASPCallback CallBackErrors) ;
    PubKeyServer_Cb     : ASP_Address -> PubKeyCallback ;
    PlcServer_Cb        : ASP_Address -> PlcCallback ;
    UUIDServer_Cb       : ASP_Address -> UUIDCallback ;

    (* Server Addresses *)
    ASPServer_Addr    : ASP_Address ;
    PubKeyServer_Addr : ASP_Address ;
    PlcServer_Addr    : ASP_Address ;
    UUIDServer_Addr   : ASP_Address ;

    (* Local Mappings *)
    Local_ASPS        : MapC ASP_ID (ASPCallback CallBackErrors) ;
    Local_Appraisal_ASPS : MapC (Plc * ASP_ID) (ASPCallback CallBackErrors) ;

    Local_Plcs        : MapD Plc UUID ;
    Local_PubKeys     : MapD Plc PublicKey ;
  }.

Record AM_Config : Type := 
  mkAmConfig {
    absMan : Manifest ;
    aspCb : (ASPCallback DispatcherErrors) ;
    app_aspCb : (ASPCallback DispatcherErrors) ;
    plcCb : PlcCallback ;
    pubKeyCb : PubKeyCallback ;
    uuidCb : UUIDCallback ;
  }.

Definition empty_aspCb (ps:ASP_PARAMS) (p:Plc) (bs:BS) (rawev:RawEv) : ResultT BS DispatcherErrors := 
  errC Unavailable.

  Definition empty_am_config : AM_Config :=
  mkAmConfig 
    empty_Manifest
    empty_aspCb
    empty_aspCb
    (fun x => errC Unavailable)
    (fun x => errC Unavailable)
    (fun x => errC Unavailable).

