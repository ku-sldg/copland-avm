Require Import String Maps EqClass.

Require Import List.
Require Import StructTactics.
Require Import Lia.


Inductive JSON :=
| JSON_Object   : Map string JSON -> JSON
| JSON_Array    : list JSON -> JSON
| JSON_String   : string -> JSON
| JSON_Boolean  : bool -> JSON.

Definition depth_js_array (ls:list JSON) (f:JSON -> nat) : nat := 
    fold_right (fun js acc => max acc (f js)) 0 ls.

Definition depth_js_map (m: Map string JSON) (f:JSON -> nat) : nat := 
  fold_right (fun pr acc => max acc (f (snd pr))) 0 m.

Lemma depth_item_leq_array_max : forall (ls:list JSON) (f:JSON -> nat) (js:JSON),
  In js ls -> f js <= depth_js_array ls f.
Proof.
  induction ls; simpl; intuition; subst; eauto.
  - lia.
  - eapply (IHls f) in H0; lia.
Qed.

Lemma depth_item_leq_map_max : forall (m : Map string JSON) (f:JSON -> nat) (js:JSON),
  In js (map snd m) -> f js <= depth_js_map m f.
Proof.
  induction m; simpl; intuition; subst; eauto; simpl in *.
  - lia.
  - eapply (IHm f) in H0; lia.
Qed.

Fixpoint JSON_depth (js:JSON) : nat := 
  match js with
  | JSON_Boolean _ => 1 
  | JSON_String _ => 1 
  | JSON_Array ls => 1 + depth_js_array ls JSON_depth
  | JSON_Object m => 1 + depth_js_map m JSON_depth
  end.

Theorem JSON_ind_better (P : JSON -> Prop)
  (fmap : forall m : Map string JSON, 
    (forall (v:JSON), In v (map snd m) -> P v) -> P (JSON_Object m))
  (flist : forall l : list JSON, (forall v, In v l -> P v) -> P (JSON_Array l))
  (fstring : forall s : string, P (JSON_String s))
  (fbool : forall b : bool, P (JSON_Boolean b)) :
  forall j : JSON, P j.
Proof.
  assert (forall x : JSON, (forall y : JSON, (fun j1 j2 => JSON_depth j1 < JSON_depth j2) y x -> P y) -> P x). {
    intros js F; destruct js eqn:?; eauto.
    - subst; eapply fmap; intros; eapply F; simpl.
      pose proof (depth_item_leq_map_max m JSON_depth v H); lia.
    - subst; eapply flist; intros; eapply F; simpl.
      pose proof (depth_item_leq_array_max l JSON_depth v H); lia.
  }
  assert (well_founded (fun j1 j2 => JSON_depth j1 < JSON_depth j2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  eapply well_founded_ind; eauto.
Qed.

Fixpoint eqb_json `{EqClass string, EqClass bool} (js1 js2:JSON) : bool := 
  match js1, js2 with
  | JSON_Object m1, JSON_Object m2 => map_eqb_eqb eqb_json m1 m2
  | JSON_Array ls1, JSON_Array ls2 => list_eqb_eqb eqb_json ls1 ls2
  | JSON_String s1, JSON_String s2 => eqb s1 s2
  | JSON_Boolean b1, JSON_Boolean b2 => eqb b1 b2
  | _, _ => false
  end.

Theorem eqb_json_eq : forall `{EqClass string, EqClass bool} js1 js2, 
  eqb_json js1 js2 = true <-> js1 = js2.
Proof.
  induction js1 using JSON_ind_better;
  destruct js2; simpl in *; try (split; intros; congruence).
  - erewrite map_eqb_eq; eauto; split; intros; subst; try congruence.
  - erewrite list_eqb_eq; eauto; split; intros; congruence.
  - rewrite eqb_eq; intuition; subst; eauto; inversion H1; eauto.
  - rewrite eqb_eq; intuition; subst; eauto; inversion H1; eauto.
Qed.

Global Instance EqClass_JSON `{EqClass string, EqClass bool} : EqClass JSON := 
{
  eqb := eqb_json;
  eqb_eq := eqb_json_eq;
}.


(*
Inductive JSON :=
| JSON_Object     : Map string InnerJSON -> JSON

with InnerJSON :=
| InJSON_Object   : JSON -> InnerJSON
| InJSON_Array    : list InnerJSON -> InnerJSON
| InJSON_String   : string -> InnerJSON
| InJSON_Boolean  : bool -> InnerJSON.

*)