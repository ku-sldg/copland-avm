(* Functions surrounding Negotiation for DEMO 

   Roughly, code will: 
   1. pass in protocol
   2. ensure protocol is sound and executable 

*)

Require Import Manifest. 
Require Import Term.

Require Import String. 

Require Import List.
Import ListNotations.
Require Import Params_Admits Term_Defs Eqb_Evidence AbstractedTypes EqClass.


(**** Ltac used *)

Ltac inverts t := inversion t; subst; clear t.
Ltac right_dest_contr H := right; unfold not; intros H; destruct H; contradiction.
Ltac right_intro_inverts := right; unfold not; intros H'; inverts H'.
Ltac right_dest_inverts := right; unfold not; intros H; inverts H.

(** [Environment] is a set of AM's each defined by a [Manifest].
  The domain of an [Environment] provides names for each [Manifest].
  Names should be the hash of their public key, but this restriction
  is not enforced here. 
*)

Definition Environment : Type :=  Plc -> (option Manifest).

Definition e_empty : Environment := (fun _ => None).

Print Plc. 

Definition e_update `{H : EqClass ID_Type} (m : Environment) (x : Plc) (v : (option Manifest)) :=
  fun x' => if eqb x x' then v else m x'.

(** A [System] is all attestation managers in the enviornement *)

Definition System := list Environment.

(** ****************************
  * REASONING ABOUT MANIFESTS
*****************************)

(** Within the enviornment [e], does the AM at place [k] have ASP [a]? *)

Definition hasASPe(k:Plc)(e:Environment)(a:ASP_ID):Prop :=
match (e k) with
| None => False
| Some m => In a m.(asps)
end.      

(** Within the system [s], does the AM located at place [k] have ASP [a]? *)

Fixpoint hasASPs(k:Plc)(s:System)(a:ASP_ID):Prop :=
    match s with
    | [] => False
    | s1 :: s2 => (hasASPe k s1 a) \/ (hasASPs k s2 a)
    end.

(** Proof that hasASPe is decidable. This means, for any enviornment [e] 
   either the ASP [a] is present or it's not. *)

(** Decidable equality proofs for various Copland datatypes *)
Definition eq_asp_id_dec `{H : EqClass ID_Type} :
  forall x y: ASP_ID, {x = y} + {x <> y}.
Proof.
  intros.
  eapply EqClass_impl_DecEq; eauto.
Defined.

Theorem hasASPe_dec `{H : EqClass ID_Type} : forall k e a, {hasASPe k e a}+{~hasASPe k e a}.
Proof.
  intros k e a.
  unfold hasASPe.
  destruct (e k).
  + induction (asps m).
  ++ auto.
  ++ inverts IHl.
  +++ simpl. left. right. apply H0.
  +++ simpl. assert (asp_dec : {a = a0} + {a<>a0}). 
           { apply eq_asp_id_dec. }    
      inverts asp_dec.
  ++++ left. auto.
  ++++ right. unfold not. intros. inverts H2; auto.
  + auto.      
Defined.

(** prove hasASPs is decidable. This means, for any system [s] 
   either the ASP [a] is present or it's not. *)

Theorem hasASPs_dec: forall k e a, {hasASPs k e a}+{~hasASPs k e a}.
Proof.
  intros k e a.
  induction e.
  + simpl in *. right. unfold not. intros. apply H.
  + simpl in *. pose proof hasASPe_dec k a0 a. inverts H. 
  ++ left. left. apply H0.
  ++ inverts IHe.
  +++ left. right. apply H.
  +++ right. unfold not. intros. inverts H1; auto.
Defined. 

(** Determine if manifest [k] from [e] knows how to 
   communicate from [k] to [p]
*)

Definition knowsOfe(k:Plc)(e:Environment)(p:Plc):Prop :=
match (e k) with
| None => False
| Some m => In p m.(knowsOf)
end.

Print System.
Print Environment.

(** Determine if place [k] within the system [s] knows of [p] *)

Fixpoint knowsOfs(k:Plc)(s:System)(p:Plc):Prop :=
match s with
| [] => False
| s1 :: s2 => (knowsOfe k s1 p) \/ (knowsOfs k s2 p)
end.
(* need this second k to change.... *)


(** Prove knowsOfe is decidable. This means, for any enviornment [e] 
   either the current place [p] is aware of place [p] or it's not.  *)

Theorem knowsOfe_dec:forall k e p, {(knowsOfe k e p)}+{~(knowsOfe k e p)}.
Proof.
  intros k e p.
  unfold knowsOfe.
  destruct (e k); auto.
  + induction (knowsOf m).
  ++ auto.
  ++ assert (H: {p = a} + {p <> a}). { apply eq_asp_id_dec. }
     inversion H.
  +++ simpl. left. auto.
  +++ simpl. inverts IHl; auto. right. unfold not. intros. inverts H2; auto.
Defined.

(** decidability of knowsOfs. For any system [s], either [k] knows 
   of [p] within the system or they do not. *)

Theorem knowsOfs_dec:forall k s p, {(knowsOfs k s p)}+{~(knowsOfs k s p)}.
Proof.
    intros k s p.
    induction s; simpl in *.
    + right. unfold not. intros. inversion H.     
    + pose proof knowsOfe_dec k a p. inverts H.
    ++ left. left. apply H0.
    ++ inverts IHs.
    +++ left. right. apply H.
    +++ right. unfold not. intros. inversion H1; auto.
Defined. 

(** Determine if place [k] within the environment [e]  
    depends on place [p] (the context relation) *)
Definition dependsOne (k:Plc)(e:Environment)(p:Plc):Prop :=
match (e k) with
| None => False
| Some m => In p m.(context)
end.

(** Determine if place [k] within the system [s] depends on place [p] (the context relation) *)

Fixpoint dependsOns (k:Plc)(s:System)(p:Plc):Prop :=
match s with
| [] => False
| s1 :: s2 => (dependsOne k s1 p) \/ (dependsOns k s2 p)
end.

(** decidability of dependsOne. For any enviornment [e], either the AM at place
   [k] depends on something at place [p] or it does not. *)

Theorem dependsOne_dec : forall k e p, {(dependsOne k e p)}+{~(dependsOne k e p)}.
Proof.
  intros k e p.
  unfold dependsOne.
  destruct (e k).
  +  induction (context m).
  ++ auto.
  ++ simpl. inversion IHl.
  +++  auto.
  +++ assert (H': {a = p } + { a <> p}). { apply eq_asp_id_dec. } inversion H'.
  ++++ left. left. apply H0.
  ++++ right. unfold not. intros. inversion H1; auto.
  + auto.
Defined.

(** decidability of dependsOns. For any system [s], either the AM at place [k] depends on something at place [p] or it does not. *)

Theorem dependsOns_dec : forall k s p, {dependsOns k s p} + {~ dependsOns k s p}.
Proof.
  intros. induction s. 
  + simpl. auto.
  + simpl. pose proof dependsOne_dec k a p. inversion IHs.
  ++ left. right. apply H0. 
  ++ inversion H.
  +++ left. left. apply H1.
  +++ right. unfold not. intros. inversion H2; auto.
Defined. 

(** ***************************
    * EXECUTABILITY 
*****************************)


(** Is term [t] exectuable on the attestation manager named [k] in 
    environment [e]?  Are ASPs available at the right attesation managers
    and are necessary communications allowed? *)

Print ASP_ID.

Fixpoint executable(t:Term)(k:Plc)(e:Environment):Prop :=
match t with
| asp a  => match a with 
            | ASPC _ _ p => match p with 
                            | asp_paramsC aspid _ _ _ => hasASPe k e aspid
                            end
            | NULL => False
            | CPY => False
            | SIG => False
            | HSH => False
            | ENC p => False
            end
| att p t => knowsOfe k e p -> executable t p e
| lseq t1 t2 => executable t1 k e /\ executable t2 k e
| bseq _ t1 t2 => executable t1 k e /\ executable t2 k e
| bpar _ t1 t2 => executable t1 k e /\ executable t2 k e
end.

(* Ltac right_dest_contr H := right; unfold not; intros H; destruct H; contradiction.
Ltac right_dest_inverts := right; unfold not; intros H; inverts H. *)

(** executability of a term is decidable *)

Theorem executable_dec:forall t k e,{(executable t k e)}+{~(executable t k e)}.
intros.  generalize k. induction t; intros.
+ destruct a; try auto. destruct a.  unfold executable.  apply hasASPe_dec.
+ simpl. pose proof knowsOfe_dec k0 e p. destruct H.
++ destruct (IHt p).
+++ left; auto.
+++ right. unfold not. intros; auto.
++ destruct (IHt p).
+++ left; auto. 
+++ left. intros. congruence.
+ simpl. specialize IHt1 with k0. specialize IHt2 with k0. 
  destruct IHt1,IHt2; try right_dest_contr H. 
++ left. split ; assumption.
+ simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H. 
++ left. split ; assumption.
+ simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H.
++  left. split ; assumption.
Defined.

(******************************
*        POLICY
*******************************)

(** Check environment [e] and see if place [p] has some policy 
 *  where the Policy allows p to run a. *)
Definition checkASPPolicy(p:Plc)(e:Environment)(a:ASP):Prop :=
match (e p) with (* Look for p in the environment *)
| None => False
| Some m => (policy m a p) (* Policy from m allows p to run a *)
end.

(** Recursive policy check. *)
Fixpoint checkTermPolicy(t:Term)(k:Plc)(e:Environment):Prop :=
  match t with
  | asp a  => checkASPPolicy k e a
  | att r t0 => checkTermPolicy t0 k e
  | lseq t1 t2 => checkTermPolicy t1 k e /\ checkTermPolicy t2 k e
  | bseq _ t1 t2 => checkTermPolicy t1 k e /\ checkTermPolicy t2 k e
  | bpar _ t1 t2 => checkTermPolicy t1 k e /\ checkTermPolicy t2 k e
  end.

(** Proving policy check is decidable. 
  * This is true if ASP policy is decidable. *)
Theorem checkTermPolicy_dec:forall t k e,
    (forall p0 a0, {(checkASPPolicy p0 e a0)} + {~(checkASPPolicy p0 e a0)}) ->
    {(checkTermPolicy t k e)}+{~(checkTermPolicy t k e)}.
Proof.
  intros t k e.
  intros H.
  induction t.
  + simpl. apply H.
  + simpl. assumption.
  + simpl; destruct IHt1,IHt2.
  ++ left. split; assumption.
  ++ right_dest_contr H'.
  ++ right_dest_contr H'.
  ++ right_dest_contr H'.
  + simpl; destruct IHt1,IHt2.
  ++ left. split; assumption.
  ++ right_dest_contr H'.
  ++ right_dest_contr H'.
  ++ right_dest_contr H'.
  + simpl; destruct IHt1,IHt2.
  ++ left. split; assumption.
  ++ right_dest_contr H'.
  ++ right_dest_contr H'.
  ++ right_dest_contr H'. 
Defined.


(** ***************************
 * SOUND
 *****************************)

(** Soundness is executability and policy adherence *)

Definition sound (t:Term)(k:Plc)(e:Environment) :=
  (executable t k e) /\ (checkTermPolicy t k e).

(** Prove soundness is decidable with the assumption necessary for policy
 * adherence decidability.
 *)

 Theorem sound_dec: forall t p e,
 (forall p0 a0, {(checkASPPolicy p0 e a0)} + {~(checkASPPolicy p0 e a0)})
 -> {sound t p e}+{~(sound t p e)}.
Proof.
  intros t p e.
  intros H.
  unfold sound.
  assert ({executable t p e}+{~(executable t p e)}). apply executable_dec.
  assert ({checkTermPolicy t p e}+{~(checkTermPolicy t p e)}). { apply checkTermPolicy_dec. intros. apply H. }
  destruct H0,H1.
  + left. split; assumption.
  + right_dest_contr H'.
  + right_dest_contr H'.
  + right_dest_contr H'.
Defined.

(** ***************************
 * EXAMPLE SYSTEM 
 *****************************)

(** Motivated by the Flexible Mechanisms for Remote Attestation, 
 * we have three present parties in this attestation scheme. 
 * These are used for example purposes.
 *)

Notation P0 := "P0"%string.
Notation P1 := "P1"%string.
Notation P2 := "P2"%string.

(** Introducing three asps for testing purposes. *)
Notation aVC :=
  (ASPC ALL EXTD (asp_paramsC "aVC"%string ["x"%string] P1 P1)).
Notation aHSH :=
  (ASPC ALL EXTD (asp_paramsC "aHSH"%string ["x"%string] P1 P1)).
Notation aSFS :=
  (ASPC ALL EXTD (asp_paramsC "aSFS"%string ["x"%string] P2 P2)).

(** Below are relational definitions of Policy. Within the definition, we
 * list each ASP on the AM and state who can recieve a measurement of said
 * ASP (ie doesn't expose sensitive information in the context).
 * 
 * The relying party (P0) has no measurement to write policy over. 
 * P1 can share the measurement aHSH and aVC with P0
 * P2 can share a measurement using aSFS with P1 
*)

Inductive tar_Policy : ASP -> Plc -> Prop := 
| p_aHSH : tar_Policy aHSH P2 
| p_SIG : forall p, tar_Policy SIG p. 

Inductive P0_Policy : ASP -> Plc -> Prop :=.

Inductive P1_Policy : ASP -> Plc -> Prop :=
| aVC_p: P1_Policy aVC P0
| aHSH_p: P1_Policy aHSH P0. 

Inductive P2_Policy : ASP -> Plc -> Prop :=
| aSFS_pL: P2_Policy aSFS P1.

Global Hint Constructors P0_Policy : core.
Global Hint Constructors P1_Policy : core.
Global Hint Constructors P2_Policy : core.

(** Definition of environments for use in examples and proofs.  
 * Note there are 3 communicating peer's present... 
 * P0, P1, and P2.
 *)

Definition e0 := e_empty.
Definition e_P0 :=
    e_update e_empty P0 (Some {| asps := []; K:= [P1] ; C := [] ; Policy := P0_Policy |}).
Definition e_P1 :=
    e_update e_P0 P1 (Some {| asps := [aVC;  aHSH]; K:= [P2] ; C := [] ; Policy := P1_Policy|}).
Definition e_P2 :=
    e_update e_P1 P2 (Some {| asps := [aSFS] ; K:= [] ; C := [P1] ; Policy := P2_Policy |}).

(** In our example, the system includes the relying party, the target,
 * and the appraiser
 *)

Definition example_sys_1 := [e_P0; e_P1; e_P2]. 

(** ***************************
  * EXAMPLE SYSTEM PROPERTIES
  *****************************)

(** Prove the P0 knows of P1 in P0's enviornment *)

Example ex1: knowsOfe P0 e_P0 P1.
Proof. unfold knowsOfe. simpl. left. reflexivity. Qed.

(** relying party does not have the ASP aVC *)

Example ex2: hasASPe P0 e_P0 aVC -> False.
Proof. unfold hasASPe. simpl. intros. inverts H. Qed.

(** Prove the P1 can generate a term with aHSH within the system *)

Example ex3: hasASPs P1 (example_sys_1) aVC.
Proof. simpl. unfold hasASPe. simpl. auto. Qed. 

(** the P0 knows of the target within system 1
 *)

Example ex4: knowsOfs P0 example_sys_1 P1.
Proof.
unfold knowsOfs. simpl. left. unfold knowsOfe. simpl.  auto.
Qed.

(** the P0 does not directly know of the appraiser
 *)

Example ex5: knowsOfe P0 e_P2 P2 -> False.
Proof.
  unfold knowsOfe. simpl. intros. destruct H. inversion H. assumption.
Qed.

(** the P0 does not knows of the P2 within the system... 
 * should be that P0 knows of P1 and P1
 * knows of P2....
 *)

Example ex6: knowsOfs P0 example_sys_1 P2 -> False.
Proof.
unfold knowsOfs. simpl. unfold knowsOfe. simpl. intros. inverts H. inverts H0. inverts H. apply H. inverts H0. destruct H. inverts H. apply H. destruct H. inverts H. inverts H0. apply H0. apply H.
Qed.

(** if the P0 was it's own system, it would still be aware of
 *  P1 *)

Example ex7: knowsOfs P0 [e_P0] P1.
Proof.
unfold knowsOfs,knowsOfe. simpl. auto.
Qed.

(** Proof tactic for executability
 *)
Ltac prove_exec' :=
    simpl; auto; match goal with
                 | |- hasASPe _ _ _ => cbv; left; reflexivity
                 | |- knowsOfe _ _ _ => unfold knowsOfe; simpl; left; reflexivity
                 | |- _ /\ _ => split; prove_exec'
                 | |- ?A => idtac A
                 end.

(** Is asp aVC executable on the P1 in the P1s's
 * enviornement?
 *)

Example ex8: (executable (asp aVC) P1 e_P1).
Proof. prove_exec'. Qed.

(** aSFS is not executable on P1 even if in P2's environment
 *)

Example ex9: (executable (asp aSFS) P1 e_P2) -> False.
Proof.
  intros Hcontra; cbv in *; destruct Hcontra. inverts H. destruct H. inverts H. apply H.
Qed.

(** two aHSH operations are executable on the P1
 *)

Example ex10: (executable (lseq (asp aHSH) (asp aHSH)) P1 e_P1).
Proof. prove_exec'; cbv; auto. Qed.

(** the relying party can ask the target to run aVC and signature
 * operations within system 1
 *) 

Example ex11: (executables (lseq (asp aVC) (att P1 (lseq (asp aHSH) (asp aHSH)))) P1 example_sys_1).
Proof. 
  prove_exec'; cbv; auto. intros. split; auto. 
Qed.

(* A few decidability proofs... useful later*)
Theorem string_dec: forall (s s':string), {s=s'}+{s<>s'}.
Proof.
  intros s s'.
  repeat decide equality.
Defined.

Theorem plc_dec: forall (p p':Plc),{p=p'}+{p<>p'}.
Proof.
  intros p p'.
  apply string_dec.
Defined.

(** A proof that [tar_Policy] is decidable.  If we can show all policies are
* decidable, life is good.  This is a start.
*)
Theorem tar_Policy_dec: forall (asp:ASP)(plc:Plc), {(tar_Policy asp plc)}+{~(tar_Policy asp plc)}.
Proof.
  intros asp.
  intros plc.
  destruct asp.
  + right_dest_inverts.
  + right_dest_inverts.
  + pose proof ASP_dec (ASPC s f a) aHSH.
    pose proof plc_dec plc P2.
    destruct H; destruct H0.
  ++ subst. left. rewrite e. apply p_aHSH.
  ++ right. rewrite e. unfold not in *. intros Hneg. apply n. inversion Hneg. reflexivity.
  ++ right. unfold not in *. intros Hneg. apply n. inversion Hneg. reflexivity.
  ++ right. unfold not in *. intros Hneg. apply n. inversion Hneg. reflexivity.
  + left. apply p_SIG.
  + right_dest_inverts.
Defined.

(* Policy P0 is decidable *)
Theorem P0_Policy_dec: forall (asp:ASP)(plc:Plc), {(P0_Policy asp plc)}+{~(P0_Policy asp plc)}.
Proof.
  intros asp; intros plc; destruct asp; right_dest_inverts.
Defined.
  
(* Policy P1 is decidable *)
Theorem P1_Policy_dec: forall (asp:ASP)(plc:Plc), {(P1_Policy asp plc)}+{~(P1_Policy asp plc)}.
  intros asp.
  intros plc.
  destruct asp. 
  + right_dest_inverts.
  + right_dest_inverts.
  + pose proof ASP_dec (ASPC s f a) aHSH.
    pose proof ASP_dec (ASPC s f a) aVC.
    pose proof plc_dec plc P0.
    destruct H; destruct H0; destruct H1; subst.
  ++ rewrite e in e1. inversion e1.
  ++ rewrite e in e1. inversion e1.
  ++ rewrite e. auto.
  ++ right_dest_inverts. contradiction. contradiction.
  ++ rewrite e. left. auto.
  ++ right_dest_inverts; contradiction.
  ++ right_dest_inverts; contradiction.
  ++ right_dest_inverts; contradiction.
  + right_dest_inverts.
  + right_dest_inverts.
Defined.
  
(* Policy P2 is decidable *)
Theorem P2_Policy_dec: forall (asp:ASP)(plc:Plc), {(P2_Policy asp plc)}+{~(P2_Policy asp plc)}.
Proof.
  intros asp.
  intros plc.
  destruct asp.
  + right_dest_inverts.
  + right_dest_inverts.
  + pose proof ASP_dec (ASPC s f a) aSFS.
    pose proof plc_dec plc P1.
    destruct H,H0.
  ++ left. subst. rewrite e. auto.
  ++ right_dest_inverts; contradiction.
  ++ right_dest_inverts; contradiction.
  ++ right_dest_inverts; contradiction.
  + right_dest_inverts.
  + right_dest_inverts.
Defined.

Ltac map_update_eq := unfold e_P2; apply e_update_reduce; unfold not; intros Hneg; rewrite Hneg in *; contradiction.

(* With Policy, we can now prove the system (e_P2) is sound. *)
Theorem sound_local_policies: (forall p0 a0, {(checkASPPolicy p0 e_P2 a0)} + {~(checkASPPolicy p0 e_P2 a0)}).
Proof.
  intros p a.
  pose proof plc_dec p P0.
  pose proof plc_dec p P1. 
  pose proof plc_dec p P2. 
  destruct H, H0, H1.
  + rewrite e in e1. inversion e1.
  + rewrite e in e1. inversion e1.
  + rewrite e in e1. inversion e1.
  + rewrite e. unfold checkASPPolicy. simpl. apply P0_Policy_dec.
  + rewrite e in e1. inversion e1.
  + rewrite e. unfold checkASPPolicy. simpl. apply P1_Policy_dec.
  + rewrite e. unfold checkASPPolicy. simpl. apply P2_Policy_dec.
  + right. unfold checkASPPolicy. 
   assert (H: e_P2 p = e_P1 p). { map_update_eq. }
   assert (H0: e_P1 p = e_P0 p). { map_update_eq. }
   assert (H1: e_P0 p = e_empty p). { map_update_eq. }
   unfold not. intros Hneg. rewrite <- H in *. rewrite <- H0 in *. rewrite H1 in *. auto.
Defined.

(* Proof that the system described by e_P2 is sound. *)
Theorem sound_system_dec: forall t p, {sound t p e_P2}+{~(sound t p e_P2)}.
Proof.
  intros t p.
  apply sound_dec.
  intros p0 a0.
  apply sound_local_policies.
Defined.

Compute sound_system_dec (asp aHSH) P1.
Compute sound_system_dec (asp aSFS) P2.


