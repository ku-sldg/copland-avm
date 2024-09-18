(** Basic definitions for Copland terms, Core terms, 
   EvidenceT Types, and Copland events. *)

(*
   These definitions have been adapted from an earlier version, archived 
   here:  https://ku-sldg.github.io/copland/resources/coplandcoq.tar.gz 

   with License:

LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Export BS.

Require Import List ID_Type Maps JSON Stringifiable Stringifiable_Class_Admits StructTactics
  ErrorStringConstants.
Require Import EqClass.
Import ListNotations ResultNotation.

(** * Terms and EvidenceT *)

(** [Plc] represents a place (or attestation domain). *)
Definition Plc: Set := ID_Type.
(** [N_ID] represents a nonce identifier.  *)
Definition N_ID: Set := nat.
(** [Event_ID] represents Event identifiers *)
Definition Event_ID: Set := nat.

(** [ASP_ID], [TARG_ID], and [Arg] are all identifiers and parameters to ASP terms
    [ASP_ID] identifies the procedure invoked.
    [TARG_ID] identifies the target (when a target makes sense).
    [Arg] represents a custom argument for a given ASP 
          (defined and interpreted per-scenario/implementaiton).
*)
Definition ASP_ID: Set := ID_Type.
Definition ASP_Compat_MapT := Map ASP_ID ASP_ID.
Definition ASP_ARGS := Map string string.

Definition TARG_ID: Set := ID_Type.

(** Grouping ASP parameters into one constructor *)
Inductive ASP_PARAMS: Type :=
| asp_paramsC: ASP_ID -> ASP_ARGS -> Plc -> TARG_ID -> ASP_PARAMS.

Definition eqb_ASP_PARAMS `{EqClass ASP_ID, EqClass ASP_ARGS, EqClass Plc, EqClass TARG_ID}
    (a1 a2 : ASP_PARAMS) : bool :=
  let '(asp_paramsC a1 la1 p1 t1) := a1 in
  let '(asp_paramsC a2 la2 p2 t2) := a2 in
  (eqb a1 a2) && (eqb la1 la2) && (eqb p1 p2) && (eqb t1 t2).

Global Instance EqClass_ASP_PARAMS `{EqClass ASP_ID, EqClass ASP_ARGS, EqClass Plc, EqClass TARG_ID} : EqClass ASP_PARAMS.
eapply Build_EqClass with (eqb := eqb_ASP_PARAMS).
induction x; destruct y; ff;
repeat rewrite Bool.andb_true_iff in *; ff;
repeat rewrite eqb_eq in *; ff.
Defined.

(** EvidenceT extension types for ASPs:
      COMP:  Compact EvidenceT down to a single value (i.e. a hash).
      ENCR:  Like COMP, but the single value is semantically an ENCRYPTED one.
      EXTD:  Extend bundle (non-destructively) by prepending the new ASP result to the front.
      KILL:  Ignore EvidenceT produced by an ASP and put Mt EvidenceT.
      KEEP:  Ignore EvidenceT produced by an ASP and keep the input EvidenceT unchanged.


COMP:  [b1, b2, ..., bn] ==> [hash([b1, b2, ..., bn])]
ENCR:  [b1, b2, ..., bn] ==> [encrypt([b1, b2, ..., bn])]
EXTD:  [b1, b2, ..., bn] ==> f([b1, b2, ..., bn]) ++ [b1, b2, ..., bn]], 
            where f represents the ASP's functional result over an input EvidenceT bundle.
KILL:  [b1, b2, ..., bn] ==> []
KEEP:  [b1, b2, ..., bn] ==> [b1, b2, ..., bn]
*)
Inductive FWD :=
| REPLACE
| WRAP
| UNWRAP
| EXTEND.

Inductive EvInSig :=
| InAll : EvInSig
| InNone : EvInSig.

Inductive EvOutSig :=
| OutN : nat -> EvOutSig
| OutUnwrap : EvOutSig.

Inductive EvSig :=
| ev_arrow : FWD -> EvInSig -> EvOutSig -> EvSig.

(** The structure of EvidenceT. 

    mt_evt:  Empty EvidenceT 
    nn:  Nonce EvidenceT (with an ID)
    uu:  ASP EvidenceT bundle
    ss:  EvidenceT pairing (composition)
*)
Inductive EvidenceT :=
| mt_evt      : EvidenceT
| nonce_evt   : N_ID -> EvidenceT
| asp_evt     : Plc -> ASP_PARAMS -> EvidenceT -> EvidenceT
| left_evt    : EvidenceT -> EvidenceT
| right_evt   : EvidenceT -> EvidenceT
| split_evt   : EvidenceT -> EvidenceT -> EvidenceT.

Fixpoint eqb_EvidenceT `{EqClass N_ID, EqClass ASP_PARAMS, EqClass Plc} (e1 e2 : EvidenceT) : bool :=
  match e1, e2 with
  | mt_evt, mt_evt => true
  | nonce_evt i, nonce_evt i' => eqb i i'
  | asp_evt p par e, asp_evt p' par' e' =>
    (eqb p p') && (eqb par par') && (eqb_EvidenceT e e')
  | left_evt e, left_evt e' => eqb_EvidenceT e e'
  | right_evt e, right_evt e' => eqb_EvidenceT e e'
  | split_evt e1 e2, split_evt e1' e2' =>
    eqb_EvidenceT e1 e1' && eqb_EvidenceT e2 e2'
  | _, _ => false
  end.

Global Instance EqClass_EvidenceT `{EqClass N_ID, EqClass Plc, EqClass ASP_PARAMS} : EqClass EvidenceT.
eapply Build_EqClass with (eqb := eqb_EvidenceT).
induction x, y; simpl in *; ff;
repeat rewrite Bool.andb_true_iff in *; ff;
repeat rewrite eqb_eq in *; ff;
try erewrite IHx in *; ff;
try erewrite IHx1, IHx2 in *; ff.
Defined.

(** Evidene routing types:  
      ALL:   pass through all EvidenceT
      NONE   pass through empty EvidenceT
*)
Inductive SP: Set :=
| ALL
| NONE.

(** Primitive Copland phases 

    NULL:    Empty out EvidenceT (optionally with a strong "zeroize" effect)
    CPY:     Copy EvidenceT (leave input EvidenceT unchanged)
    ASPC sp fwd ps:    
        Arbitrary ASPs:
          sp indicates passing ALL or NONE as input EvidenceT.
          fwd indicates how to extend output EvidenceT.
          ps indicates the asp parameters structure
    SIG:     Signature primitive
    HSH:     Hash primitive 
    ENC q:   Encryption primitive using public key associated with place q.
*)
Inductive ASP :=
| NULL: ASP
| ASPC: ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP
| APPR : ASP
| ENC: Plc -> ASP.

Definition ASP_Type_Env := Map ASP_ID EvSig.

Record GlobalContext := {
  asp_types: ASP_Type_Env;
  asp_comps: ASP_Compat_MapT
}.

(* Definition get_type (G : GlobalContext) (a : ASP_ID) : ResultT EvSig string :=
  match map_get a (asp_types G) with
  | Some t => resultC t
  | None => errC err_str_asp_no_type_sig
  end.

Definition get_compat_asp (G : GlobalContext) (a : ASP_ID) 
    : ResultT ASP_ID string :=
  match map_get a (asp_comps G) with
  | Some t => resultC t
  | None => errC err_str_asp_no_compat_appr_asp
  end. *)

(** Pair of EvidenceT splitters that indicate routing EvidenceT to subterms 
    of branching phrases *)
Definition Split: Set := (SP * SP).

(** Pair of EvidenceT splitters that indicate routing EvidenceT to subterms 
    of branching phrases *)

(** Main Copland phrase datatype definition.
        A term is either an atomic ASP (Attestation Service Provider), 
        a remote call (att), a sequence of terms with data a dependency (lseq),
        a sequence of terms with no data dependency, or parallel terms. *)
Inductive Term :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

Open Scope string_scope.

Definition EvidenceT_depth : EvidenceT -> nat :=
  fix F e :=
  match e with
  | mt_evt => 0
  | nonce_evt _ => 0
  | asp_evt _ _ e' => 1 + F e'
  | left_evt e' => 1 + F e'
  | right_evt e' => 1 + F e'
  | split_evt e1 e2 => 1 + max (F e1) (F e2)
  end.

Require Import Lia.

Lemma EvidenceT_double_ind (P : EvidenceT -> Prop) 
    (f_mt : P mt_evt) 

    (f_nonce : forall n : N_ID, P (nonce_evt n))

    (f_asp_mt : forall p a, P (asp_evt p a mt_evt))
    (f_aps_nonce : forall p a n, P (asp_evt p a (nonce_evt n)))
    (f_asp_asp : forall (e : EvidenceT), P e -> 
      forall p p' a a', P (asp_evt p a (asp_evt p' a' e)))
    (f_asp_left : forall p a e, P (left_evt e) -> P (asp_evt p a (left_evt e)))
    (f_asp_right : forall p a e, P (right_evt e) -> P (asp_evt p a (right_evt e)))
    (f_asp_split : forall p a e1 e2, P e1 -> P e2 -> P (asp_evt p a (split_evt e1 e2)))

    (f_left_mt : P (left_evt mt_evt))
    (f_left_nonce : forall n : N_ID, P (left_evt (nonce_evt n)))
    (f_left_asp_mt : forall p a, P (left_evt (asp_evt p a mt_evt)))
    (f_left_asp_nonce : forall p a n, P (left_evt (asp_evt p a (nonce_evt n))))
    (f_left_asp_asp : forall e, P (left_evt e) -> 
      forall p a p' a', P (left_evt (asp_evt p a (asp_evt p' a' e))))
    (f_left_asp_left : forall e, P (left_evt e) -> 
      forall p a, P (left_evt (asp_evt p a (left_evt e))))
    (f_left_asp_right : forall e, P (right_evt e) -> 
      forall p a, P (left_evt (asp_evt p a (right_evt e))))
    (f_left_asp_split : forall e1 e2, P e1 -> P e2 -> 
      forall p a, P (left_evt (asp_evt p a (split_evt e1 e2))))
    (f_left_left : forall e : EvidenceT, P (left_evt e) -> P (left_evt (left_evt e)))
    (f_left_right : forall e : EvidenceT, P (right_evt e) -> P (left_evt (right_evt e)))
    (f_left_split : forall e1 e2 : EvidenceT, 
      P e1 -> 
      P (left_evt (split_evt e1 e2)))

    (f_right_mt : P (right_evt mt_evt))
    (f_right_nonce : forall n : N_ID, P (right_evt (nonce_evt n)))
    (f_right_asp_mt : forall p a, P (right_evt (asp_evt p a mt_evt)))
    (f_right_asp_nonce : forall p a n, P (right_evt (asp_evt p a (nonce_evt n))))
    (f_right_asp_asp : forall e, P (right_evt e) -> 
      forall p a p' a', P (right_evt (asp_evt p a (asp_evt p' a' e))))
    (f_right_asp_left : forall e, P (left_evt e) -> 
      forall p a, P (right_evt (asp_evt p a (left_evt e))))
    (f_right_asp_right : forall e, P (right_evt e) -> 
      forall p a, P (right_evt (asp_evt p a (right_evt e))))
    (f_right_asp_split : forall e1 e2, P e1 -> P e2 -> 
      forall p a, P (right_evt (asp_evt p a (split_evt e1 e2))))
    (f_right_left : forall e : EvidenceT, P e -> P (right_evt (left_evt e)))
    (f_right_right : forall e : EvidenceT, P e -> P (right_evt (right_evt e)))
    (f_right_split : forall e1 e2 : EvidenceT, 
      P e2 -> 
      P (right_evt (split_evt e1 e2)))

    (f_split : forall e : EvidenceT, P e -> 
      forall e0 : EvidenceT, P e0 -> P (split_evt e e0)) 
    : forall e, P e.
  assert (well_founded (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  assert (forall x : EvidenceT, (forall y : EvidenceT, (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2) y x -> P y) -> P x). {
    destruct x; simpl in *; eauto; intros F.
    - destruct x; eauto.
      eapply f_asp_split; eapply F; simpl in *; eauto; lia.
    - destruct x; eauto.
      * destruct x; eauto.
        (* ** eapply f_left_asp_asp; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_left_asp_left; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_left_asp_right; eapply F; simpl in *; eauto; lia. *)
        ** eapply f_left_asp_split; eapply F; simpl in *; eauto; lia.
      * eapply f_left_split; eapply F; eauto; simpl in *; lia.
    - destruct x; eauto.
      * destruct x; eauto.
        (* ** eapply f_right_asp_asp; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_right_asp_left; eapply F; simpl in *; eauto; lia. *)
        (* ** eapply f_right_asp_right; eapply F; simpl in *; eauto; lia. *)
        ** eapply f_right_asp_split; eapply F; simpl in *; eauto; lia.
      * eapply f_right_split; eapply F; eauto; simpl in *; lia.
    - eapply f_split; eapply F; simpl in *; eauto; lia.
  }
  eapply well_founded_ind; eauto.
Qed.

Definition get_left_evt (G : GlobalContext) 
    : EvidenceT -> ResultT EvidenceT string :=
  fix F e :=
  match e with
  | split_evt e1 e2 => resultC e1
  | asp_evt _ (asp_paramsC a' _ _ _) (
      asp_evt _ (asp_paramsC a _ _ _) e'
    ) => 
    (* if a and a' are duals, and they are a WRAP *)
    match (map_get a (asp_comps G)) with
    | None => errC err_str_asp_no_compat_appr_asp
    | Some a'' =>
      if (eqb a' a'') 
      then (* they are duals, is a a WRAP *)
        match (map_get a (asp_types G)) with
        | None => errC err_str_asp_no_type_sig
        | Some (ev_arrow WRAP _ _) => 
          match (map_get a' (asp_types G)) with
          | None => errC err_str_asp_no_type_sig
          | Some (ev_arrow UNWRAP _ _) => F e'
          | _ => errC err_str_appr_asp_not_unwrap
          end
        | _ => errC err_str_asp_is_not_wrap
        end
      else errC (err_str_asps_not_duals)
    end
  | _ => errC err_str_no_possible_left_evt
  end.

Definition apply_to_left_evt {A : Type} (G : GlobalContext) 
    (f : EvidenceT -> A) : EvidenceT -> ResultT A string :=
  fix F e :=
  match e with
  | split_evt e1 e2 => resultC (f e1)
  | asp_evt _ (asp_paramsC a' _ _ _) (
      asp_evt _ (asp_paramsC a _ _ _) e'
    ) => 
    (* if a and a' are duals, and they are a WRAP *)
    match (map_get a (asp_comps G)) with
    | None => errC err_str_asp_no_compat_appr_asp
    | Some a'' =>
      if (eqb a' a'') 
      then (* they are duals, is a a WRAP *)
        match (map_get a (asp_types G)) with
        | None => errC err_str_asp_no_type_sig
        | Some (ev_arrow WRAP _ _) => 
          match (map_get a' (asp_types G)) with
          | None => errC err_str_asp_no_type_sig
          | Some (ev_arrow UNWRAP _ _) => F e'
          | _ => errC err_str_appr_asp_not_unwrap
          end
        | _ => errC err_str_asp_is_not_wrap
        end
      else errC (err_str_asps_not_duals)
    end
  | _ => errC err_str_no_possible_left_evt
  end.

Lemma get_left_evt_correct: forall {A : Type} G e e' (fn : EvidenceT -> A),
  get_left_evt G e = resultC e' ->
  apply_to_left_evt G fn e = resultC (fn e').
Proof.
  induction e using EvidenceT_double_ind; simpl in *;
  ff; result_monad_unfold; ff.
Qed.

Lemma apply_to_left_evt_correct: forall {A : Type} G e e' (fn : EvidenceT -> A),
  apply_to_left_evt G fn e = resultC e' ->
  exists e'', fn e'' = e'.
Proof.
  induction e using EvidenceT_double_ind; simpl in *;
  ff; result_monad_unfold; ff.
Qed.

Lemma apply_to_left_evt_deterministic: forall {A B : Type} G e e' (fn : EvidenceT -> A) (fn' : EvidenceT -> B),
  apply_to_left_evt G fn e = resultC e' ->
  exists e'', apply_to_left_evt G fn' e = resultC e''.
Proof.
  induction e using EvidenceT_double_ind; simpl in *;
  ff; result_monad_unfold; ff.
Qed.

Definition apply_to_right_evt {A : Type} (G : GlobalContext) 
    (f : EvidenceT -> A) : EvidenceT -> ResultT A string :=
  fix F e :=
  match e with
  | split_evt e1 e2 => resultC (f e2)
  | asp_evt _ (asp_paramsC a' _ _ _) (
      asp_evt _ (asp_paramsC a _ _ _) e'
    ) => 
    (* if a and a' are duals, and they are a WRAP *)
    match (map_get a (asp_comps G)) with
    | None => errC err_str_asp_no_compat_appr_asp
    | Some a'' =>
      if (eqb a' a'') 
      then (* they are duals, is a a WRAP *)
        match (map_get a (asp_types G)) with
        | None => errC err_str_asp_no_type_sig
        | Some (ev_arrow WRAP _ _) => 
          match (map_get a' (asp_types G)) with
          | None => errC err_str_asp_no_type_sig
          | Some (ev_arrow UNWRAP _ _) => F e'
          | _ => errC err_str_appr_asp_not_unwrap
          end
        | _ => errC err_str_asp_is_not_wrap
        end
      else errC (err_str_asps_not_duals)
    end
  | _ => errC err_str_no_possible_right_evt
  end.

(** Calculate the size of an ASP's input based on its signature *)
(* Definition asp_sig_et_size (previous_sig : EvSig) (sig : EvSig) 
    : ResultT nat string :=
  let '(ev_arrow fwd in_sig out_sig) := sig in
  match fwd with
  | REPLACE => 
    (* we are replacing, so just the output *)
    match out_sig with
    | OutN n => n
    | OutDepIn => errC err_str_invalid_signature
    end
  | WRAP => 
    (* we are wrapping, so just the output *)
    match out_sig with
    | OutN n => n
    | OutDepIn => errC err_str_invalid_signature
    end
  | UNWRAP => 
    (* we are unwrapping, so we are the size of the previous input *)
    match out_sig with
    | OutN n => errC err_str_invalid_signature
    | OutDepIn => size_in
    end
  | EXTEND => 
    match 
  end. *)

Definition get_asp_under (G : GlobalContext) :
    EvidenceT -> ResultT EvidenceT string :=
  fix F e :=
  match e with
  | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
    (* we either want to:
    1. If this is not an UNWRAP we can just return it *)
    match (map_get top_id (asp_types G)) with
    | None => errC err_str_asp_no_type_sig
    | Some (ev_arrow fwd in_sig out_sig) =>
      match fwd with
      | UNWRAP =>
        (* This was an UNWRAP, so we need to be able to get below it *)
        match et' with
        | asp_evt _ (asp_paramsC bury_id _ _ _) et'' =>
          match (map_get bury_id (asp_comps G)) with
          | None => errC err_str_asp_no_compat_appr_asp
          | Some bury_id' =>
            if (eqb top_id bury_id') 
            then 
              match (map_get bury_id (asp_types G)) with
              | None => errC err_str_asp_no_type_sig
              | Some (ev_arrow fwd' _ _) =>
                match fwd' with
                | WRAP => F et''
                | _ => errC err_str_asp_under_unwrap
                end
              end
            else errC err_str_wrap_asp_not_duals
          end
        | _ => errC err_str_unwrap_only_asp
        end
      | _ => resultC e
      end
    end
  | left_evt et' => r <- apply_to_left_evt G F et' ;; r
  | right_evt et' => r <- apply_to_right_evt G F et' ;; r
  | _ => errC err_str_no_asp_under_evidence
  end.

Definition apply_to_asp_under_wrap {A : Type} (G : GlobalContext) 
    (unwrap_id : ASP_ID) (f : EvidenceT -> A)
    : EvidenceT -> ResultT A string :=
  fix F e :=
  match e with
  | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
    (* we either want to:
    1. If this is not an UNWRAP we can just return it *)
    match (map_get top_id (asp_types G)) with
    | None => errC err_str_asp_no_type_sig
    | Some (ev_arrow UNWRAP _ _) => 
      (* This was an UNWRAP, so we need to be able to get below it *)
      match et' with
      | asp_evt _ (asp_paramsC bury_id _ _ _) et'' =>
        match (map_get bury_id (asp_comps G)) with
        | None => errC err_str_asp_no_compat_appr_asp
        | Some bury_id' =>
          if (eqb top_id bury_id') 
          then 
            match (map_get bury_id (asp_types G)) with
            | None => errC err_str_asp_no_type_sig
            | Some (ev_arrow WRAP _ _) => F et''
            | _ => errC err_str_asp_under_unwrap
            end
          else errC err_str_wrap_asp_not_duals
        end
      | _ => errC err_str_unwrap_only_asp
      end
    | Some (ev_arrow WRAP _ _) => 
      (* if this is an WRAP, and they are compat, we are done *)
      match (map_get top_id (asp_comps G)) with
      | None => errC err_str_asp_no_compat_appr_asp
      | Some unwrapper_id =>
        if (eqb unwrapper_id unwrap_id) 
        then resultC (f e)
        else errC err_str_wrap_asp_not_duals
      end
    | Some _ => errC err_str_asp_at_bottom_not_wrap
    end
  | left_evt et' => r <- apply_to_left_evt G F et' ;; r
  | right_evt et' => r <- apply_to_right_evt G F et' ;; r
  | _ => errC err_str_no_asp_under_evidence
  end.
  

(**  Calculate the size of an EvidenceT type *)
Definition et_size (G : GlobalContext) : EvidenceT -> ResultT nat string :=
  fix F e :=
  match e with
  | mt_evt=> resultC 0
  | nonce_evt _ => resultC 1
  | asp_evt p par e' =>
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (map_get asp_id (asp_types G)) with
    | None => errC err_str_asp_no_type_sig
    | Some (ev_arrow fwd in_sig out_sig) =>
      match fwd with
      | REPLACE => 
        (* we are replacing, so just the output *)
        match out_sig with
        | OutN n => resultC n
        | OutUnwrap => errC err_str_cannot_have_outwrap
        end
      | WRAP => 
        (* we are wrapping, so just the output *)
        match out_sig with
        | OutN n => resultC n
        | OutUnwrap => errC err_str_cannot_have_outwrap 
        end
      | UNWRAP => 
        (* we are unwrapping, so we are the size of the previous input *)
        match out_sig with
        | OutN n => errC err_str_unwrap_must_have_outwrap
        | OutUnwrap => 
          match e' with
          | (asp_evt p (asp_paramsC asp_id' args' targ_plc' targ') e'') =>
            match (map_get asp_id' (asp_types G)) with
            | None => errC err_str_asp_no_type_sig
            | Some (ev_arrow WRAP in_sig' out_sig') =>
              match in_sig' with
              | InAll => 
                n' <- F e'' ;;
                resultC n'
              | InNone => resultC 0
              end
            | _ => errC err_str_unwrap_only_wrap
            end
          | _ => errC err_str_unwrap_only_asp
          end
        end
      | EXTEND =>
        match out_sig with
        | OutN n => 
          n' <- F e' ;;
          resultC (n + n')
        | OutUnwrap => errC err_str_cannot_have_outwrap 
        end
      end
    end
  | left_evt e' => r <- apply_to_left_evt G F e' ;; r

  | right_evt e' => r <- apply_to_right_evt G F e' ;; r

  | split_evt e1 e2 => 
    s1 <- F e1 ;; 
    s2 <- F e2 ;;
    resultC (s1 + s2)
  end.
Close Scope string_scope.

(* 
Fixpoint appr_et_size (G : GlobalContext) (e : EvidenceT) : ResultT nat string :=
  match e with
  | mt_evt => resultC 0
  | nonce_evt _ => resultC 2 (* umeas check_nonce :: nonce *)
  | asp_evt p par e' =>
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (map_get (asp_comps G) asp_id) with
    | None => errC err_str_asp_no_compat_appr_asp
    | Some appr_asp_id =>
      match (map_get (asp_types G) appr_asp_id) with
      | None => errC err_str_asp_no_type_sig
      | Some (ev_arrow fwd in_sig (OutN n)) => 
        match asp_si with
        | COMP => resultC 2 (* This asp crushed down to 1, then +1 for appr *)
        | ENCR => resultC 2 (* this asp crushed down to 1, then +1 for appr *)
        | (EXTD n) => 
          n' <- et_size G e' ;; (* this asp operates on stuff of size n' *)
          resultC (1 + n + n') (* they return n + n', then +1 for appr on top *)
        | KILL => resultC 0 (* this asp returns only mt_evc, which is appr as mt_evc too *)
        | KEEP => 
          n <- et_size G e' ;; (* this asp operates on stuff of size n, and returns of size n *)
          resultC (1 + n) (* they returned n, we do +1 for appr on top *)
        end
      end
    end
  | split_evt e1 e2 =>
    s1 <- appr_et_size G e1 ;;
    s2 <- appr_et_size G e2 ;;
    resultC (s1 + s2)
  end.
  *)

(** Raw EvidenceT representaiton:  a list of binary (BS) values. *)
Definition RawEv := list BS.

(**  Type-Tagged Raw EvidenceT representation.  Used as the internal EvidenceT
     type managed by the CVM to track EvidenceT contents and its structure. *)
Inductive Evidence :=
| evc: RawEv -> EvidenceT -> Evidence.

Definition mt_evc: Evidence := (evc [] mt_evt).

Definition get_et (e:Evidence) : EvidenceT :=
  match e with
  | evc ec et => et
  end.

Definition get_bits (e:Evidence): list BS :=
  match e with
  | evc ls _ => ls
  end.

(** A "well-formed" Evidence value is where the length of its raw EvidenceT portion
    has the proper size (calculated over the EvidenceT Type portion). *)
Inductive wf_Evidence : GlobalContext -> Evidence -> Prop :=
| wf_Evidence_c: forall (ls:RawEv) et G n,
    List.length ls = n ->
    et_size G et = resultC n ->
    wf_Evidence G (evc ls et).

Inductive CopPhrase :=
| cop_phrase : Plc -> EvidenceT -> Term -> CopPhrase.

(* Adapted from Imp language Notation in Software Foundations (Pierce) *)
Declare Custom Entry copland_entry.
Declare Scope cop_ent_scope.
Notation "<{ e }>" := e (at level 0, e custom copland_entry at level 99) : cop_ent_scope.
Notation "( x )" := x (in custom copland_entry, x at level 99) : cop_ent_scope.
Notation "x" := x (in custom copland_entry at level 0, x constr at level 0) : cop_ent_scope.
(* Branches*)
Notation "x -<- y" := (bseq (NONE, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +<- y" := (bseq (ALL, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -<+ y" := (bseq (NONE, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +<+ y" := (bseq (ALL, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -~- y" := (bpar (NONE, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +~- y" := (bpar (ALL, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -~+ y" := (bpar (NONE, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +~+ y" := (bpar (ALL, ALL) x y) (in custom copland_entry at level 70, right associativity).
(* ARROW sequences *)
Notation "x -> y" := (lseq x y) (in custom copland_entry at level 99, right associativity).
(* ASP's *)
Notation "!" := (asp SIG) (in custom copland_entry at level 98).
Notation "#" := (asp HSH) (in custom copland_entry at level 98).
Notation "* p" := (asp (ENC p)) (in custom copland_entry at level 98).
Notation "'{}'" := (asp NULL) (in custom copland_entry at level 98).
(* TODO: Surely we need something more robust than they are ALL EXTD 1, but uhhhh *)
Notation "'<<' x y z '>>'" := (asp (ASPC (asp_paramsC x nil y z))) 
                      (in custom copland_entry at level 98).


(* @ plc phrase *)
Notation "@ p [ ph ]" := (att p ph) (in custom copland_entry at level 50).

(** Abstract Location identifiers used to aid in management and execution 
    of parallel Copland phrases. *)
Definition Loc: Set := nat.
Definition Locs: Set := list Loc.

