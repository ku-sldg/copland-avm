Require Import NegotiationDefs NegotiationDefs_Prop NegotiationDefs_Bool
               Manifest Eqb_Evidence Term_Defs_Core.

Require Import Example_Phrases_Admits Example_Phrases.

Require Import Utilities EqClass Maps.


Require Import StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.


(*
Set Nested Proofs Allowed.
*)


(********************
  *   HAS APS PROOFS 
  ********************)

(* Proof that hasASPe is decidable *)
Theorem hasASPe_dec: forall k e a, {hasASPe k e a}+{~hasASPe k e a}.
Proof.
  intros k e a.
  unfold hasASPe.
  destruct (e k); auto.
  + induction (asps m); auto.
  ++ pose proof eq_aspid_dec a a0; inverts H; simpl.
  +++ left. auto.
  +++ destruct IHl.
  ++++ left. auto.
  ++++ right_intro_inverts; auto.
Defined.

(* prove hasASPs is decidable *)
Theorem hasASPs_dec: forall k e a, {hasASPs k e a}+{~hasASPs k e a}.
Proof.
  intros k e a.
  induction e; simpl.
  + right. unfold not; auto.
  + pose proof hasASPe_dec k a0 a; inverts H. 
  ++ left; auto.
  ++ inverts IHe.
  +++ left; auto.
  +++ right_intro_inverts; auto.
Defined.    
  
(********************
  *  KNOWS OF PROOFS 
  ********************)

(* Prove knowsOfe is decidable *)
Theorem knowsOfe_dec:forall k e p, {(knowsOfe k e p)}+{~(knowsOfe k e p)}.
Proof.
  intros k e p.
  unfold knowsOfe.
  destruct (e k); auto.
  induction (uuidPlcs m).
  + right; auto. 
  + pose proof (eq_plc_dec p a); inverts H. 
  ++ left. simpl. auto.
  ++ inverts IHl.
  +++ simpl. left; auto.
  +++ right_intro_inverts; auto. 
Qed.

(* decidability of knowsOfs*)
Theorem knowsOfs_dec:forall k s p, {(knowsOfs k s p)}+{~(knowsOfs k s p)}.
Proof.
  intros k s p.
  induction s; simpl in *.
  + right_intro_inverts.     
  + pose proof knowsOfe_dec k a p. inverts H.
  ++ left. left. apply H0.
  ++ inverts IHs.
  +++ left. right. apply H.
  +++ right_intro_inverts; auto.
Qed. 

(********************
*  DEPENDS ON PROOFS 
********************)

(* depends on (context relation) is decidable *)
Theorem dependsOne_dec : forall k e p, {(dependsOne k e p)}+{~(dependsOne k e p)}.
Proof with auto.
  intros k e p.
  unfold dependsOne.
  destruct (e k) ...
  + induction (pubKeyPlcs m).
  ++ auto.
  ++ simpl. inversion IHl.
  +++ auto.
  +++ pose proof eq_plc_dec a p. inversion H0.
  ++++ left ...
  ++++ right_intro_inverts ...
Defined.        

Theorem dependsOns_dec : forall k s p, {dependsOns k s p} + {~ dependsOns k s p}.
Proof with auto.
  intros. induction s. 
  + simpl...
  + simpl. pose proof dependsOne_dec k a p. inversion IHs.
  ++ left. right. apply H0. 
  ++ inversion H.
  +++ left. left. apply H1.
  +++ right_intro_inverts... 
Defined.

Lemma canRunAsp_Manifest_prop_iff_bool : forall e a,
    canRunAsp_ManifestB e a = true <-> canRunAsp_Manifest e a.
Proof.
  intros.
  split.
  - (* -> case *)
    unfold canRunAsp_Manifest.
    unfold canRunAsp_ManifestB.
    destruct e.
    destruct a.
    intros.
    find_apply_lem_hyp andb_prop.
    destruct_conjs.
    split.
    + 
      eapply existsb_eq_iff_In.
      eassumption.
    +
      eauto.
  - (* <- case *)
    unfold canRunAsp_Manifest.
    unfold canRunAsp_ManifestB.
    destruct e.
    destruct a.
    intros.
    destruct_conjs.
    find_rewrite.
    rewrite <- existsb_eq_iff_In in H.
    rewrite Bool.andb_true_r.
    eassumption.
Qed.

Lemma knowsOf_Manifest_prop_iff_bool: forall e a,
    knowsOf_ManifestB e a = true <-> knowsOf_Manifest e a.
Proof.
  intros.
  split;
    unfold knowsOf_Manifest in * ;
    unfold knowsOf_ManifestB in * ;
    apply existsb_eq_iff_In; auto.
Qed.

Lemma executable_prop_iff_bool : forall t e,
    executableB t e = true <-> executable t e.
Proof.
  intros.
  split.
  - (* -> case *)
  generalizeEverythingElse t.
  induction t; intros;

    (* lseq, bseq, bpar cases... *)
    try (
        simpl in *;
        specialize IHt1 with (e:=e);
        specialize IHt2 with (e:=e);
        split;
          try (apply IHt1);
          try (apply IHt2);
          find_apply_lem_hyp andb_prop;
          destruct_conjs;
          eassumption).

  + (* asp case *)
    destruct a; simpl in *; try tauto.
    ++
      rewrite <- canRunAsp_Manifest_prop_iff_bool.
      eauto.
  + (* at case *)
    simpl in *.
    rewrite <- knowsOf_Manifest_prop_iff_bool.
    eauto.

  - (* <- case *)
    generalizeEverythingElse t.
    induction t; intros;

      (* lseq, bseq, bpar cases... *) 
      try (
          simpl in *;
          specialize IHt1 with (e:=e);
          specialize IHt2 with (e:=e);
          destruct H;
          repeat find_apply_hyp_hyp;
          repeat find_rewrite;
          tauto).

    + (* asp case *)
      destruct a; simpl in *; try tauto.
      ++
        rewrite canRunAsp_Manifest_prop_iff_bool.
        eauto.
    + (* at case *)
      simpl in *.
      rewrite knowsOf_Manifest_prop_iff_bool.
      eauto.
Qed.


Theorem executable_dec : forall t e, {executable t e} + {~ executable t e}.
Proof.
  intros.
  destruct (executableB t e) eqn:H.
  -
    left.
    rewrite <- executable_prop_iff_bool.
    eassumption.
  -
    right.
    rewrite <- executable_prop_iff_bool.
    rewrite H.
    auto.
Qed.


(* Definition Environment : Type :=  Plc -> (option Manifest). *)
Definition Environment : Type := MapC Plc Manifest.

Definition e_empty : Environment := [] (*map_empty *). (* (fun _ => None). *)
  
(*
Definition e_update (e : Environment) (x : Plc) (v : (option Manifest)) : Environment :=
    fun x' => if eqb x x' then v else e x'.

Definition e_get (e : Environment) (x : Plc) : (option Manifest) := 
  e x.
  *)


Definition aspid_manifest_update (i:ASP_ID) (m:Manifest) : Manifest := 
  let '{| my_abstract_plc := oldPlc;
          asps := oldasps; 
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          policy := oldPolicy (*; 
          ac_policy := oldAcPol*) |} := m in
  (Build_Manifest oldPlc (i::oldasps) oldKnowsOf oldContext oldPolicy (*oldAcPol*)).

Definition knowsof_manifest_update (toPlc:Plc) (m:Manifest) : Manifest := 
    let '{| my_abstract_plc := oldPlc;
            asps := oldasps; 
            uuidPlcs := oldKnowsOf; 
            pubKeyPlcs := oldContext; 
            policy := oldPolicy (*; 
            ac_policy := oldAcPol*) |} := m in
    (Build_Manifest oldPlc oldasps (toPlc::oldKnowsOf) oldContext oldPolicy (*oldAcPol*)).

Definition knowsof_myPlc_manifest_update (m:Manifest) : Manifest :=
  let '{| my_abstract_plc := oldPlc;
          asps := oldasps; 
          uuidPlcs := oldKnowsOf; 
          pubKeyPlcs := oldContext; 
          policy := oldPolicy (*; 
          ac_policy := oldAcPol*) |} := m in
    (Build_Manifest oldPlc oldasps (oldPlc::oldKnowsOf) oldContext oldPolicy (*oldAcPol*)).

Definition myPlc_manifest_update (p:Plc) (m:Manifest) : Manifest := 
      let '{| my_abstract_plc := _;
              asps := oldasps; 
              uuidPlcs := oldKnowsOf; 
              pubKeyPlcs := oldContext; 
              policy := oldPolicy (*; 
              ac_policy := oldAcPol*) |} := m in
      (Build_Manifest p oldasps oldKnowsOf oldContext oldPolicy (*oldAcPol*)).

Definition asp_manifest_update (a:ASP) (m:Manifest) : Manifest :=
  match a with 
  | ASPC _ _ params => 
      match params with
      | asp_paramsC i _ targp targid => 
          aspid_manifest_update i m
      end
  | _ => m 
  end.
        
Definition asp_manifest_generator (a:ASP) (p:Plc) (e:Environment) : Environment :=
  match (map_get e p) with
  | Some m => 
    let m' := asp_manifest_update a m in 
      map_set e p m'
  | _ => 
    let m' := asp_manifest_update a empty_Manifest in 
      map_set e p m'
  end.

  Definition plc_manifest_generator (fromPlc:Plc) (toPlc:Plc) (e:Environment) : Environment :=
    match (map_get e fromPlc) with
    | Some m => 
      let m' := knowsof_manifest_update toPlc m in 
        map_set e fromPlc m'
    | _ => 
      let m' := knowsof_manifest_update toPlc empty_Manifest in 
        map_set e fromPlc m'
    end.


Fixpoint manifest_generator' (t:Term) (p:Plc) (e:Environment) : Environment :=
  match t with
  | asp a => asp_manifest_generator a p e
  | att q t' => 
      let e' := plc_manifest_generator p q e in 
        manifest_generator' t' q e'
  | lseq t1 t2 => manifest_generator' t2 p (manifest_generator' t1 p e)
  | bseq _ t1 t2 => manifest_generator' t2 p (manifest_generator' t1 p e)
  | bpar _ t1 t2 => manifest_generator' t2 p (manifest_generator' t1 p e)
  end.


Definition manifest_generator (t:Term) (p:Plc) : Environment :=
  manifest_generator' t p e_empty.


Fixpoint places' (t:Term) (ls:list Plc) : list Plc :=
  match t with
  | asp _ => ls 
  | att q t' => (q :: (places' t' ls))
  | lseq t1 t2 => places' t2 (places' t1 ls)
  | bseq _ t1 t2 => places' t2 (places' t1 ls)
  | bpar _ t1 t2 => places' t2 (places' t1 ls)
  end.

Definition places (t:Term) (p:Plc) : list Plc := 
  p :: (places' t []).


Definition fromSome{A:Type} (v:option A) (a:A) : A :=
  match v with 
  | Some v' => v'
  | _ => a 
  end.

Definition get_manifest_env_default (e:Environment) (p:Plc) : Manifest :=
  let m' := fromSome (map_get e p) empty_Manifest in
    myPlc_manifest_update p m'.

  Check List.map.
  (* map
	 : forall A B : Type, (A -> B) -> list A -> list B
   *)

Definition get_unique_manifests_env' (ps:list Plc) (e:Environment) : list Manifest :=
  List.map (get_manifest_env_default e) ps.

Definition get_unique_manifests_env (t:Term) (p:Plc) (e:Environment) : list Manifest :=
  let ps := places t p in
    get_unique_manifests_env' ps e.

Definition get_final_manifests_env (t:Term) (p:Plc) (e:Environment) : list Manifest :=
  let ms := get_unique_manifests_env t p e in 
  List.map (knowsof_myPlc_manifest_update) ms.


Definition man_gen_run (t:Term) (p:Plc) : Environment := manifest_generator t p.

Definition environment_to_manifest_list (e:Environment) : list Manifest :=
  map_vals e.

Definition demo_man_gen_run (t:Term) (p:Plc) : list Manifest := 
  get_final_manifests_env t p (man_gen_run t p).



Definition man_gen_res : Manifest := (fromSome (map_get (man_gen_run cert_style P0) P1) empty_Manifest).
Compute man_gen_res.

Compute man_gen_run.


(*
Example mytest : (man_gen_run = map_empty).
Proof.
  cbv.
  break_let.
  assert (eqb P2 P1 = false).
  admit.
  find_rewrite.
  simpl.
  pose proof (eqb_leibniz P2 P2). intuition.
  find_rewrite.
  Abort.
*)


Eval cbv iota in (fromSome (map_get (man_gen_run cert_style P0) P1) empty_Manifest).







    

























(*  Below is prior decidability proofs (over Environments, Systems, etc... 
    ****
    ****



    
(********************
  *   EXECUTABLE 
  ********************)

(** Is term [t] exectuable on the attestation manager named [k] in
  * environment [e]?  Are ASPs available at the right attesation managers
  * and are necessary communications allowed?
  *)
Fixpoint executable(t:Term)(k:Plc)(e:Environment):Prop :=
  match t with
  | asp a  => hasASPe k e a
  | att p t => knowsOfe k e p -> executable t p e
  | lseq t1 t2 => executable t1 k e /\ executable t2 k e
  | bseq _ t1 t2 => executable t1 k e /\ executable t2 k e
  | bpar _ t1 t2 => executable t1 k e /\ executable t2 k e
  end.

(* executability of a term is decidable *)
Theorem executable_dec:forall t k e,{(executable t k e)}+{~(executable t k e)}.
  Proof with auto.
  intros.  generalize k. induction t; intros.
  + unfold executable. apply hasASPe_dec.
  + simpl. assert (H:{knowsOfe k0 e p}+{~knowsOfe k0 e p}). apply knowsOfe_dec. destruct H. destruct (IHt p).
  ++ left. intros. assumption.
  ++ right. unfold not. intros... 
  ++ simpl. assert (H:{knowsOfe k0 e p}+{~knowsOfe k0 e p}). apply knowsOfe_dec. destruct H...
  +++ left. intros. congruence. 
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H. 
  ++ left. split ; assumption...
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H.   
  ++ left. split ; assumption...
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H.   
  ++ left. split ; assumption...
Defined.

(** Is term [t] executable on the attestation mnanager named [k] in
  * system [s]?  Are ASPs available at the right attestation managers
  * and are necessary communications allowed?
  *)
Fixpoint executables(t:Term)(k:Plc)(s:System):Prop :=
  match t with
  | asp a  => hasASPs k s a
  | att p t => knowsOfs k s p -> executables t p s
  | lseq t1 t2 => executables t1 k s /\ executables t2 k s
  | bseq _ t1 t2 => executables t1 k s /\ executables t2 k s
  | bpar _ t1 t2 => executables t1 k s /\ executables t2 k s
  end.

(** Is term [t] executable on the attestation mnanager named [k] in
  * system [s]?  Are ASPs available at the right attestation managers
  * and are necessary communications allowed?
  *)

Theorem executables_dec : forall t k s, {executables t k s} + {~executables t k s}.
  Proof with auto.
  intros.  generalize k s. induction t; intros.
  + unfold executables. apply hasASPs_dec.
  + simpl. assert (H:{knowsOfs k0 s0 p}+{~knowsOfs k0 s0 p}). apply knowsOfs_dec. destruct (IHt p s0).
  ++ left. intros. assumption.
  ++ destruct H.
  +++ right. unfold not...
  +++ left. intros... congruence. 
  + simpl. specialize IHt1 with k0 s0. specialize IHt2 with k0 s0. destruct IHt1,IHt2; try right_dest_contr H.
  ++  left. split ; assumption.
  + simpl. specialize IHt1 with k0 s1. specialize IHt2 with k0 s1. destruct IHt1,IHt2; try right_dest_contr H.
  ++  left. split ; assumption. 
  + simpl. specialize IHt1 with k0 s1. specialize IHt2 with k0 s1. destruct IHt1,IHt2; try right_dest_contr H.
  ++  left. split ; assumption.
  Defined.

  (******************************
*        POLICY
*******************************)

(** Check environment [e] and see if place [p] has some policy 
 *  where the Policy allows p to run a. *)
Definition checkASPPolicy (sa : SA) (p:Plc) (e:Environment) (a:ASP) :Prop :=
  match (e p) with (* Look for p in the environment *)
  | None => False
  | Some m => (Policy m a sa.(src)) (* Policy from m allows p to run a *)
  end.
  
(** Recursive policy check. *)
Fixpoint checkTermPolicy (sa : SA)(t:Term)(k:Plc)(e:Environment):Prop :=
  match t with
  | asp a  => checkASPPolicy sa k e a
  | att r t0 => checkTermPolicy sa t0 r e
  | lseq t1 t2 => checkTermPolicy sa t1 k e /\ checkTermPolicy sa t2 k e
  | bseq _ t1 t2 => checkTermPolicy sa t1 k e /\ checkTermPolicy sa t2 k e
  | bpar _ t1 t2 => checkTermPolicy sa t1 k e /\ checkTermPolicy sa t2 k e
  end.

Theorem policy_dec : forall a (sa:SA) m, {Policy m a sa.(dest)} + {~Policy m a sa.(dest)} .
Proof.
  intros. generalize m sa. induction a; destruct (dest sa); simpl.
  + destruct m. simpl. intros. 
  (* How do I get Policy0 to be a specific instance of policy? 
     Is there a better way to define it so that its decidable? *) 
Abort. 

Theorem checkASPPolicy_dec : forall sa p e a, {checkASPPolicy sa p e a} + {~checkASPPolicy sa p e a}.
Proof.
  intros.
  unfold checkASPPolicy.
  destruct (e p); try auto.
  unfold Policy. destruct m. 
Abort.

(** Proving policy check is decidable. 
  * This is true if ASP policy is decidable. *)
Theorem checkTermPolicy_dec:forall t k e sa,
    (forall p0 a0 sa0, {(checkASPPolicy sa0 p0 e a0)} + {~(checkASPPolicy sa0 p0 e a0)}) ->
    {(checkTermPolicy sa t k e)}+{~(checkTermPolicy sa t k e)}.
Proof.
  intros t k e sa.
  intros H. generalize dependent k.  
  induction t; simpl; intros. 
  + specialize H with k a sa.  apply H.
  + specialize IHt with p. assumption.  
  + specialize IHt1 with k; specialize IHt2 with k.  destruct IHt1,IHt2; try right_dest_contr H'. 
  ++ left. split; assumption.
  + specialize IHt1 with k; specialize IHt2 with k. destruct IHt1,IHt2 ; try right_dest_contr H'.
  ++ left. split; assumption.
  + specialize IHt1 with k; specialize IHt2 with k. destruct IHt1,IHt2; try right_dest_contr H'.
  ++ left. split; assumption.
Defined.

(***********
 * SOUND
 ***********)

(** Soundness is executability and policy adherence *)

Definition sound (sa:SA)(t:Term)(k:Plc)(e:Environment) :=
(executable t k e) /\ (checkTermPolicy sa t k e).

(** Prove soundness is decidable with the assumption necessary for policy
 * adherence decidability.
 *)

Theorem sound_dec: forall t p e sa,
(forall p0 a0 sa0, {(checkASPPolicy sa0 p0 e a0)} + {~(checkASPPolicy sa0 p0 e a0)})
-> {sound sa t p e}+{~(sound sa t p e)}.
Proof.
intros t p e sa. intros H. 
unfold sound. 
pose proof executable_dec t p e.
assert ({checkTermPolicy sa t p e}+{~(checkTermPolicy sa t p e)}). { apply checkTermPolicy_dec. intros. apply H. }
destruct H0,H1.
+ left. split; assumption.
+ right_dest_contr H'.
+ right_dest_contr H'.
+ right_dest_contr H'.
Defined.

End ManifestProperties.






(* End:  Prior decidability props (over environments, systems, etc...) *)

****
****
 *)
