Require Export BS.

Require Import List ID_Type Maps JSON Stringifiable Stringifiable_Class_Admits StructTactics
  ErrorStringConstants EqClass.

Require Import Term_Defs_Core.

Require Import Lia.
Import ListNotations ResultNotation.

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

Inductive EvTrails :=
| Trail_UNWRAP : ASP_ID -> EvTrails
| Trail_LEFT  : EvTrails
| Trail_RIGHT : EvTrails.

Definition apply_to_evidence_below {A} (G : GlobalContext) (f : EvidenceT -> A)
    : list EvTrails -> EvidenceT -> ResultT A string :=
  fix F trails e :=
  match trails with
  | nil => (* no further trail to follow! *)
    resultC (f e)
  | trail :: trails' =>
    match e with
    | mt_evt => errC err_str_no_evidence_below
    | nonce_evt _ => errC err_str_no_evidence_below

    | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
      match (map_get top_id (asp_types G)) with
      | None => errC err_str_asp_no_type_sig
      | Some (ev_arrow UNWRAP in_sig out_sig) =>
        (* we are UNWRAP, so add to trail and continue *)
        F ((Trail_UNWRAP top_id) :: trails) et'

      | Some (ev_arrow WRAP in_sig out_sig) =>
        (* we are a WRAP, better be the case we are looking for one *)
        match trail with
        | Trail_UNWRAP unwrap_id => 
          match (map_get top_id (asp_comps G)) with
          | None => errC err_str_asp_no_compat_appr_asp
          | Some test_unwrapping_id =>
            if (eqb test_unwrapping_id unwrap_id) 
            then (* they are compatible so we can continue on smaller *)
              F trails' et'
            else (* they are not compatible, this is a massive error *)
              errC err_str_wrap_asp_not_duals
          end
        | _ => errC err_str_trail_mismatch
        end

      | Some (ev_arrow _ in_sig out_sig) =>
        (* we are neither WRAP or UNWRAP, so this is an error *)
        errC err_str_asp_at_bottom_not_wrap
      end
    | left_evt et' => 
      (* we are pushing on a new left *)
      F (Trail_LEFT :: trails) et'

    | right_evt et' => 
      (* we are pushing on a new right *)
      F (Trail_RIGHT :: trails) et'

    | split_evt e1 e2 => 
      (* we are a split, depending on trail we will either go 
      left or right and continue *)
      match trail with
      | Trail_LEFT => F trails' e1
      | Trail_RIGHT => F trails' e2
      | _ => errC err_str_trail_mismatch
      end
    end
  end.

Require Import StructTactics.

Inductive Evidence_Subterm_path G e' : list EvTrails -> EvidenceT -> Prop :=
| esp_empty_trail : Evidence_Subterm_path G e' nil e'

| esp_unwrap : forall p in_sig out_sig e'' trails aid args targp targ,
  map_get aid (asp_types G) = Some (ev_arrow UNWRAP in_sig out_sig) ->
  Evidence_Subterm_path G e' ((Trail_UNWRAP aid) :: trails) e'' ->
  trails <> nil ->
  Evidence_Subterm_path G e' trails (asp_evt p (asp_paramsC aid args targp targ) e'')

| esp_wrap : forall p in_sig out_sig e'' trails aid args targp targ aid',
  map_get aid (asp_types G) = Some (ev_arrow WRAP in_sig out_sig) ->
  map_get aid (asp_comps G) = Some aid' ->
  Evidence_Subterm_path G e' trails e'' ->
  Evidence_Subterm_path G e' ((Trail_UNWRAP aid') :: trails) (asp_evt p (asp_paramsC aid args targp targ) e'')

| esp_left : forall e'' trails,
  Evidence_Subterm_path G e' (Trail_LEFT :: trails) e'' ->
  trails <> nil ->
  Evidence_Subterm_path G e' trails (left_evt e'')

| esp_right : forall e'' trails,
  Evidence_Subterm_path G e' (Trail_RIGHT :: trails) e'' ->
  trails <> nil ->
  Evidence_Subterm_path G e' trails (right_evt e'')

| esp_split_l : forall e1 e2 trails,
  Evidence_Subterm_path G e' trails e1 ->
  Evidence_Subterm_path G e' (Trail_LEFT :: trails) (split_evt e1 e2)

| esp_split_r : forall e1 e2 trails,
  Evidence_Subterm_path G e' trails e2 ->
  Evidence_Subterm_path G e' (Trail_RIGHT :: trails) (split_evt e1 e2).

Definition Evidence_Subterm_path_fix G e' : list EvTrails -> EvidenceT -> Prop :=
  fix F trails e :=
  match trails with
  | nil => e' = e
  | trail :: trails' =>
    match e with
    | mt_evt => False
    | nonce_evt _ => False

    | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
      match (map_get top_id (asp_types G)) with
      | None => False
      | Some (ev_arrow UNWRAP in_sig out_sig) =>
        (* we are UNWRAP, so add to trail and continue *)
        F ((Trail_UNWRAP top_id) :: trails) et'

      | Some (ev_arrow WRAP in_sig out_sig) =>
        (* we are a WRAP, better be the case we are looking for one *)
        match trail with
        | Trail_UNWRAP unwrap_id => 
          match (map_get top_id (asp_comps G)) with
          | None => False
          | Some test_unwrapping_id =>
            if (eqb test_unwrapping_id unwrap_id) 
            then (* they are compatible so we can continue on smaller *)
              F trails' et'
            else (* they are not compatible, this is a massive error *)
              False
          end
        | _ => False
        end

      | Some (ev_arrow _ in_sig out_sig) =>
        (* we are neither WRAP or UNWRAP, so this is an error *)
        False
      end
    | left_evt et' => 
      (* we are pushing on a new left *)
      F (Trail_LEFT :: trails) et'

    | right_evt et' => 
      (* we are pushing on a new right *)
      F (Trail_RIGHT :: trails) et'

    | split_evt e1 e2 => 
      (* we are a split, depending on trail we will either go 
      left or right and continue *)
      match trail with
      | Trail_LEFT => F trails' e1
      | Trail_RIGHT => F trails' e2
      | _ => False
      end
    end
  end.

(* Lemma Evidence_Subterm_path_same_fix : forall G l e e',
  Evidence_Subterm_path_fix G e' l e <->
  Evidence_Subterm_path G e' l e.
Proof.
  split; intros.
  - generalizeEverythingElse l.
    induction e; simpl in *;
    intuition; ff;
    try (exfalso; eauto; fail);
    try (eauto using Evidence_Subterm_path).
    induction H.
  - induction H;
    simpl in *; ff;
    try rewrite String.eqb_neq in *; try congruence;
    destruct e'; ff.
   *)
  
Lemma Evidence_Subterm_path_same : forall G l e e1 e2,
  Evidence_Subterm_path G e1 l e ->
  Evidence_Subterm_path G e2 l e ->
  e1 = e2.
Proof.
  intros.
  prep_induction H.
  induction H; intros; simpl in *; try (invc H0; eauto; fail).
  - invc H0; eauto; congruence.
  - invc H2; eauto; try congruence.
  - invc H2; eauto; try congruence.
  - invc H1; eauto; try congruence.
  - invc H1; eauto; try congruence.
Qed.

Definition Evidence_Subterm G e' : EvidenceT -> Prop :=
  fix F e :=
  match e with
  (* sort of a hack here, the terminals are always subterms!? *)
  | mt_evt => False
  | nonce_evt _ => False
  | asp_evt _ (asp_paramsC asp_id _ _ _) e'' => 
    match (map_get asp_id (asp_types G)) with
    | None => False
    | Some (ev_arrow UNWRAP in_sig out_sig) => 
      match apply_to_evidence_below G F [Trail_UNWRAP asp_id] e'' with
      | resultC P => P
      | errC _ => False
      end
    | Some (ev_arrow _ in_sig out_sig) => 
      e' = e''
    end
  | left_evt e'' => 
    match apply_to_evidence_below G F [Trail_LEFT] e'' with
    | resultC P => P
    | errC _ => False
    end
  | right_evt e'' => 
    match apply_to_evidence_below G F [Trail_RIGHT] e'' with
    | resultC P => P
    | errC _ => False
    end
  | split_evt e1 e2 => 
    e' = e1 \/ e' = e2 \/ F e1 \/ F e2
  end.

Lemma apply_to_evidence_below_res_spec : forall {A} G (f : _ -> A) e v l,
  apply_to_evidence_below G f l e = resultC v ->
  (exists e', Evidence_Subterm_path G e' l e /\ f e' = v).
Proof.
  induction e; simpl in *; intros; intuition; ff.
  all: eauto using Evidence_Subterm_path; ffa;
  try rewrite String.eqb_eq in *; subst; eauto.
  - exists x; split; eauto; eapply esp_wrap; eauto.
  - exists x; split; eauto; eapply esp_unwrap; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_left; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_right; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_split_l; eauto;
    intros HC; invc HC; eauto.
  - exists x; split; eauto; eapply esp_split_r; eauto;
    intros HC; invc HC; eauto.
Qed.

(* Lemma evidence_subterm_path_super : forall G e' e,
  (exists h t, Evidence_Subterm_path G e' (h :: t) e) <->
  Evidence_Subterm G e' e.
Proof.
  split; intros.
  - induction e; simpl in *; break_exists; eauto.
    * target_break_match H; subst; eauto;
      try (exfalso; eauto; fail).
      ** rewrite String.eqb_eq in *; subst.
        destruct x0.
    * admit.
    * target_break_match H; subst; ff;
      try (exfalso; eauto; fail).
  induction e; simpl in *; intros; ff. *)


(* Definition apply_to_evidence_below {A} (G : GlobalContext) (f : EvidenceT -> A)
    : list EvTrails -> EvidenceT -> ResultT A string :=
  fix F trails e :=
  match trails with
  | nil => (* no further trail to follow! *)
    resultC (f e)
  | trail :: trails' =>
    match e with
    | mt_evt => errC err_str_no_evidence_below
    | nonce_evt _ => errC err_str_no_evidence_below

    | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
      match (map_get top_id (asp_types G)) with
      | None => errC err_str_asp_no_type_sig
      | Some (ev_arrow UNWRAP in_sig out_sig) =>
        (* we are UNWRAP, so add to trail and continue *)
        F ((Trail_UNWRAP top_id) :: trails) et'

      | Some (ev_arrow WRAP in_sig out_sig) =>
        (* we are a WRAP, better be the case we are looking for one *)
        match trail with
        | Trail_UNWRAP unwrap_id => 
          match (map_get top_id (asp_comps G)) with
          | None => errC err_str_asp_no_compat_appr_asp
          | Some test_unwrapping_id =>
            if (eqb test_unwrapping_id unwrap_id) 
            then (* they are compatible so we can continue on smaller *)
              F trails' et'
            else (* they are not compatible, this is a massive error *)
              errC err_str_wrap_asp_not_duals
          end
        | _ => errC err_str_trail_mismatch
        end

      | Some (ev_arrow _ in_sig out_sig) =>
        (* we are neither WRAP or UNWRAP, so this is an error *)
        errC err_str_asp_at_bottom_not_wrap
      end
    | left_evt et' => 
      (* we are pushing on a new left *)
      F (Trail_LEFT :: trails) et'

    | right_evt et' => 
      (* we are pushing on a new right *)
      F (Trail_RIGHT :: trails) et'

    | split_evt e1 e2 => 
      (* we are a split, depending on trail we will either go 
      left or right and continue *)
      match trail with
      | Trail_LEFT => F trails' e1
      | Trail_RIGHT => F trails' e2
      | _ => errC err_str_trail_mismatch
      end
    end
  end. *)

Lemma apply_to_evidence_below_nil : forall A G (f : _ -> A) e v,
  apply_to_evidence_below G f nil e = resultC v ->
  f e = v.
Proof.
  destruct e; simpl in *; 
  intros; find_injection; eauto.
Qed.

(* Lemma apply_to_evidence_below_cons : forall A G (f : _ -> A) e t l v,
  apply_to_evidence_below G f (t :: l) e = resultC v ->
  apply_to_evidence_below G (fun e => r <- apply_to_evidence_below G f l) [t] e = resultC v.
Proof.
  intros.
  induction e; simpl in *; try simple congruence 1; eauto.
  - target_break_match H; subst; try simple congruence 1; eauto.  *)

Lemma apply_to_evidence_below_res : forall {A} G (fn1 : _ -> A) e l r,
  apply_to_evidence_below G fn1 l e = resultC r ->
  (forall {B} (fn2 : _ -> B),
    exists r', apply_to_evidence_below G fn2 l e = resultC r').
Proof.
  induction e; simpl in *; intros; ff.
Qed.

Lemma apply_to_evidence_below_errs_det : forall {A B} G (fn1 : _ -> A) (fn2 : _ -> B) e l r1 r2,
  apply_to_evidence_below G fn1 l e = errC r1 ->
  apply_to_evidence_below G fn2 l e = errC r2 ->
  r1 = r2.
Proof.
  induction e; simpl in *; intros; ff.
Qed.

(* Lemma apply_to_evidence_below_depth_id : forall {A} G (fn : _ -> A) e l1 l2 h r,
  apply_to_evidence_below G fn (l1 ++ h :: l2) e = resultC r ->
  exists e', Evidence_Subterm G e' e /\
    fn e' = r.
Proof.
  induction e; simpl in *; intros.
  - ff; try (find_eapply_lem_hyp app_eq_nil; intuition; try simple congruence 1).
  - ff; try (find_eapply_lem_hyp app_eq_nil; intuition; try simple congruence 1).
  - ff;
    try (find_eapply_lem_hyp app_eq_nil; intuition; try simple congruence 1).
    * admit.
    * admit.
  - ff;
    try (find_eapply_lem_hyp app_eq_nil; intuition; try simple congruence 1).
    pose proof (IHe nil (e0 :: l) Trail_LEFT); simpl in *.
    eapply H0 in H as ?. clear H0.
    break_exists; ff.
    exists x.
    eapply IHe in H.
    
  induction e using EvidenceT_double_ind; intros.  *)
Lemma evidence_subterm_path_nil : forall G e e',
  Evidence_Subterm_path G e' nil e ->
  e = e'.
Proof.
  intros; 
  prep_induction H; induction H; 
  intros; eauto; try congruence; ff.
Qed.

Lemma evidence_subterm_path_depth : forall G h t e e',
  Evidence_Subterm_path G e' (h :: t) e ->
  EvidenceT_depth e' < EvidenceT_depth e.
Proof.
  intros.
  prep_induction H.
  induction H; intros; try congruence; subst; ff.
  - pose proof (IHEvidence_Subterm_path _ _ eq_refl); lia.
  - destruct t; simpl in *.
    * eapply evidence_subterm_path_nil in H1; subst; lia.
    * pose proof (IHEvidence_Subterm_path _ _ eq_refl); lia.
  - pose proof (IHEvidence_Subterm_path _ _ eq_refl); lia.
  - pose proof (IHEvidence_Subterm_path _ _ eq_refl); lia.
  - destruct t; simpl in *.
    * eapply evidence_subterm_path_nil in H; subst; lia.
    * pose proof (IHEvidence_Subterm_path _ _ eq_refl); lia.
  - destruct t; simpl in *.
    * eapply evidence_subterm_path_nil in H; subst; lia.
    * pose proof (IHEvidence_Subterm_path _ _ eq_refl); lia.
Qed.

Theorem Evidence_subterm_path_Ind_special G (P : EvidenceT -> Prop)
  (f_mt : P mt_evt)
  (f_nonce : forall n, P (nonce_evt n))
  (f_subterm_asp_nowrap : forall p aid args targp targ e t isig osig,
    t <> UNWRAP ->
    map_get aid (asp_types G) = Some (ev_arrow t isig osig) ->
    P e -> 
    P (asp_evt p (asp_paramsC aid args targp targ) e))
  (f_subterm_asp : forall p aid args targp targ e isig osig, 
    map_get aid (asp_types G) = Some (ev_arrow UNWRAP isig osig) ->
    (forall l e', Evidence_Subterm_path G e' (Trail_UNWRAP aid :: l) e -> P e') ->
    P (asp_evt p (asp_paramsC aid args targp targ) e))
  (f_subterm_asp_none : forall p aid args targp targ e,
    map_get aid (asp_types G) = None ->
    P (asp_evt p (asp_paramsC aid args targp targ) e))
  (f_subterm_left : forall e, 
    (forall e' l, Evidence_Subterm_path G e' (Trail_LEFT :: l) e -> P e') -> P (left_evt e))
  (f_subterm_right : forall e, 
    (forall e' l, Evidence_Subterm_path G e' (Trail_RIGHT :: l) e -> P e') -> P (right_evt e))
  (f_split : forall e1 e2, P e1 -> P e2 -> P (split_evt e1 e2))
  : forall e, P e.
Proof.
  assert (forall x : EvidenceT, (forall y : EvidenceT, (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2) y x -> P y) -> P x). {
    intros x F; destruct x eqn:?; eauto.
    - destruct a.
      destruct (map_get a (asp_types G)) eqn:?; eauto;
      destruct e0, f; eauto.
      * eapply f_subterm_asp_nowrap; eauto; congruence.
      * eapply f_subterm_asp_nowrap; eauto; congruence.
      * eapply f_subterm_asp; eauto; intros.
        eapply F.
        find_eapply_lem_hyp evidence_subterm_path_depth; eauto.
        simpl in *; lia.
      * eapply f_subterm_asp_nowrap; eauto; congruence.
      (* eapply F. *)
      (* ff; try (exfalso; eauto; fail). *)
      (* eapply f_subterm; intros;
      ff; try (exfalso; eauto; fail).
      clear f_subterm f_mt f_split f_nonce.
      induction l.
      * destruct e' eqn:?; simpl in *; eexists; 
        split; try reflexivity. *)
      (* eapply F.
      eapply apply_to_evidence_below_res with (fn2 := id) in Heqr as ?. *)
    - 
      eapply f_subterm_left; intros.
      eapply F.
        find_eapply_lem_hyp evidence_subterm_path_depth; eauto.
        simpl in *; lia.
      (* eapply f_subterm; intros;
      ff; try (exfalso; eauto; fail). *)
      (* eapply F. *)
    - 
      eapply f_subterm_right; intros.
      eapply F.
        find_eapply_lem_hyp evidence_subterm_path_depth; eauto.
        simpl in *; lia.
      (* eapply f_subterm; intros;
      ff; try (exfalso; eauto; fail). *)
      (* eapply F. *)
    - eapply f_split; eapply F;
      simpl in *; try lia.
  } 
  assert (well_founded (fun e1 e2 => EvidenceT_depth e1 < EvidenceT_depth e2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  eapply well_founded_ind; eauto.
Qed.












































(* 
Definition apply_to_evidence_under_unwrap_wrap {A} 
    (G : GlobalContext) (f : EvidenceT -> A)
    : (list ASP_ID) -> EvidenceT -> ResultT A string :=
  fix F l e :=
  match l with
  | nil => (* we have unwrapped all *)
    resultC (f e)
  | unwrapping_id :: tl => 
    match e with
    | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
      (* we have the following cases for "top_id":
      1. It is typeless => error
      2. It is an UNWRAP itself, so we must go beneath it
      3. It is a WRAP (and compat) so we are done 
      4. It is neither a WRAP or UNWRAP, so cannot be compat => error *)
      match (map_get top_id (asp_types G)) with
      (* case 1 *)
      | None => errC err_str_asp_no_type_sig
      (* case 2: it is an UNWRAP, so we need to get beneath it 
        by pushing on a new UNWRAPPING_ID *)
      | Some (ev_arrow UNWRAP in_sig out_sig) =>
        F (top_id :: l) et'

      (* case 3: it is a WRAP, so we can maybe pop off a UNWRAP ID *)
      | Some (ev_arrow WRAP in_sig out_sig) =>
        match (map_get top_id (asp_comps G)) with
        | None => errC err_str_asp_no_compat_appr_asp
        | Some test_unwrapping_id =>
          if (eqb test_unwrapping_id unwrapping_id) 
          then (* they are compatible so we can continue on smaller *)
            F tl et'
          else (* they are not compatible, this is a massive error *)
            errC err_str_wrap_asp_not_duals
        end

      (* case 4: it is neither a WRAP or UNWRAP, but we are beneath a 
        UNWRAP id, so this must be an error *)
      | Some (ev_arrow _ in_sig out_sig) =>
        errC err_str_asp_at_bottom_not_wrap
      end
    | left_evt et' => r <- apply_to_left_evt G (F l) et' ;; r
    | right_evt et' => r <- apply_to_right_evt G (F l) et' ;; r
    | _ => (* it is an evidence type that cannot be traversed below,
      but we are in an UNWRAP still! must be an error *)
      errC err_str_no_asp_under_evidence
    end
  end.
*)

(* Definition get_left_evt (G : GlobalContext) 
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
  end. *)

(* 
Definition apply_to_left_evt {A : Type} (G : GlobalContext) 
    (f : EvidenceT -> A) : EvidenceT -> ResultT A string :=
  fix F e :=
  match e with
  | split_evt e1 e2 => resultC (f e1)
  | asp_evt _ (asp_paramsC a' _ _ _) et' =>
    apply_to_asp_under_wrap G (F) a' et'
    (* 
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
    *)
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
*)


(* Definition apply_to_asp_under_wrap {A : Type} (G : GlobalContext) 
    (f : EvidenceT -> A)
    : ASP_ID -> EvidenceT -> ResultT A string :=
  fix F e :=
  match e with
  | asp_evt _ (asp_paramsC top_id _ _ _) et' => 
    (* we have the following cases for "top_id":
    1. It is typeless => error
    2. It is an UNWRAP itself, so we must go beneath it
    3. It is a WRAP (and compat) so we are done 
    4. It is neither a WRAP or UNWRAP, so cannot be compat => error *)
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
  end. *)

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
          n' <- apply_to_evidence_below G F [Trail_UNWRAP asp_id] e' ;;
          n'
          (* match e' with
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
          end *)
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
  | left_evt e' => 
    r <- apply_to_evidence_below G F [Trail_LEFT] e' ;; 
    r

  | right_evt e' => 
    r <- apply_to_evidence_below G F [Trail_RIGHT] e' ;; 
    r

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


  (** A "well-formed" Evidence value is where the length of its raw EvidenceT portion
    has the proper size (calculated over the EvidenceT Type portion). *)
Inductive wf_Evidence : GlobalContext -> Evidence -> Prop :=
| wf_Evidence_c: forall (ls:RawEv) et G n,
    List.length ls = n ->
    et_size G et = resultC n ->
    wf_Evidence G (evc ls et).

Inductive CopPhrase :=
| cop_phrase : Plc -> EvidenceT -> Term -> CopPhrase.