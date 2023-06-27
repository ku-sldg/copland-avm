Require Import Term_Defs_Core Manifest Manifest_Generator Manifest_Generator_Facts Executable_Defs_Prop Manifest_Admits Eqb_Evidence.

Require Import List.
Import ListNotations.

Require Import StructTactics Auto.

(*
Definition Environment := Plc -> option Manifest.
*)


(********************
  *   EXECUTABLE 
  ********************)

(** Static guarentee that states: 
  * Is term [t] exectuable on the    
  * attestation manager named [k] in
  * environment [e]?  
  * Are ASPs available at the right attesation managers
  * and are necessary communications allowed?
  *)

(*
Print Manifest. 
Print Environment.
*)

Definition canRunAsp_Env (k:Plc) (em:EnvironmentM) (a: ASP_ID) : Prop := 
  match (Maps.map_get em k) with 
  | None => False 
  | Some m => In a m.(asps)
  end. 
  
  
Print EnvironmentM.
(*  Maps.MapC Plc Manifest *)

Print knowsOf_Manifest.

Definition knowsOf_Env (k:Plc)(em:EnvironmentM)(p:Plc):Prop :=
  match (Maps.map_get em k) with 
  | None => False
  | Some m => In p m.(uuidPlcs)
  end.

(* Statically, we have a global view so we can use the environement to reason about the system *)
Fixpoint executable_static (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    | asp (ASPC _ _ (asp_paramsC asp_id _ _ _))  => canRunAsp_Env k em asp_id
    | asp _ => exists m, Maps.map_get em k = Some m
    | att p t1 => knowsOf_Env k em p /\ executable_static t1 k em
    | lseq t1 t2 => executable_static t1 k em /\ executable_static t2 k em
    | bseq _ t1 t2 => executable_static t1 k em /\ executable_static t2 k em
    | bpar _ t1 t2 => executable_static t1 k em /\ executable_static t2 k em
  end.

(* A dynamic version of executabiilty. 
   At runtime, we cannot know if an att term can be executed on a remote place. *)
Fixpoint executable_dynamic (t:Term) (k:Plc) (em:EnvironmentM) : Prop := 
  match t with
    | asp (ASPC _ _ (asp_paramsC asp_id _ _ _))  => canRunAsp_Env k em asp_id
    | asp _ => True
    | att p t => knowsOf_Env k em p
    | lseq t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bseq _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
    | bpar _ t1 t2 => executable_dynamic t1 k em /\ executable_dynamic t2 k em
  end.

(*
Definition envs_eq_at (e:Environment) (em:EnvironmentM) (ps:list Plc) : Prop := 
    forall p, 
        In p ps ->
        e p = Maps.map_get em p.
*)

(* Record Manifest : Set := Build_Manifest
                            { my_abstract_plc : Plc;
                              asps : list ASP_ID;
                              uuidPlcs : list Plc;
                              pubKeyPlcs : list Plc;
                              policy : Manifest_Admits.PolicyT }.*)

(* Try to build a manifest. *)

Definition build_manifest_helper p a p1 p2 pol : Manifest := 
{|  my_abstract_plc := p ; 
    asps :=  a ;
    uuidPlcs := p1 ; 
    pubKeyPlcs := p2 ; 
    policy := pol |}. 

Lemma eqb_plc_refl : forall p0, Eqb_Evidence.eqb_plc p0 p0 = true.
Proof.
  intros. apply eqb_eq_plc. auto.
Qed.  

(* Proof that the dynamic notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_dynamic : 
    forall t p em,
      executable_static t p em -> 
      executable_dynamic t p em.
Proof.
  intros t. induction t; try ( intros; inversion H; specialize IHt1 with p em; specialize IHt2 with p em; simpl; split; auto).
  + intros. destruct a; try (apply I). auto.
  + intros. specialize IHt with p0 em. simpl in *. inversion H. apply H0.
Qed. 

Lemma top_plc_refl: forall t' p1,  In t' (place_terms t' p1 p1).
Proof.
  induction t'.
  + intros; simpl. pose proof eqb_plc_refl. specialize H with p1. rewrite H. simpl. left. auto.
  + intros. simpl in *.
Admitted. 

(* Proof that the distributed notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_distributed : 
    forall t p em,
      executable_static t p em -> 
      distributed_executability t p em.
Proof.
  intros t; induction t; intros.
  (* asp case *)
  + admit. (*  destruct a; try (apply I); auto; unfold distributed_executability; intros; simpl in *; 
    (* trys to get rid of all the asp fluf cases *)
    try (invc H; exists x; cbn in *; invc H1 ); 
    try (split; try assumption; pose proof eqb_plc_refl;
      rewrite H in H2; invc H2; try (apply I); invc H0 ); 
    try (invc H).
  ++ destruct a; try apply I; subst; simpl in *.
     invc H1.  pose proof eqb_plc_refl as H'.
  rewrite H' in H2. invc H2.
  +++ unfold canRunAsp_Env in H. destruct (Maps.map_get em p0). 
  ++++ exists m. split; auto. simpl in *. break_let. simpl in *. split; auto. cbv in *. auto.
  ++++ inversion H.
  +++ inversion H0.
  +++ inversion H0. *)
  (* @ case *)
  + invc H.   
    specialize IHt with (p := p0) (em := em). 
    unfold distributed_executability in *.
    simpl in *. intros.
    apply IHt; try assumption.
  ++ destruct H.
  +++ left. auto.
  +++ destruct H.
  ++++ rewrite H in H2. pose proof eqb_plc_refl. 
       specialize H3 with p1. rewrite H3 in H2.
       simpl in H2. inversion H2. subst. 
       simpl in *. .   
       right. simpl in H2.  



    specialize IHt with (p := p1).
    destruct H.
  ++ apply IHt with (p := p1) (t' := t'); try assumption; auto. subst.
  
  destruct (eqb_plc p1 p) eqn:eqb_plc'.
  simpl in *.  

  inversion H2. 
    destruct H2.  
  
  
  
     destruct (eqb_plc p1 p) eqn:eqb_plc'.
     apply IHt with ( p:=p1 ) (t' := t'); try assumption; auto.
     
     simpl in H2. destruct H2. 
     rewrite H2. simpl. rewrite H. pose proof top_plc_refl. apply H3.

     subst. rewrite eqb_eq_plc in eqb_plc'. subst. apply H2.  
     
     specialize IHt with ( p:=p1 ) (t' := t). try assumption; auto.

     subst. simpl in *. 
     
     
     
     
     rewrite eqb_plc'. simpl.    


    unfold knowsOf_Env in H0. destruct (Maps.map_get em p0) eqn:maps; subst; simpl in *.
    ++ destruct H2; simpl in *.
    +++ unfold places in *.    
       apply IHt with (t_places := p :: places' t []) (p := p1) (t' := t'); try auto.
    ++++  simpl in *. left. apply H.
    ++++   
    
    
    rewrite H.  reflexivity.
    ++++ simpl. left. auto.
    ++++ inversion H3.
    ++++ apply IHl. simpl in *. inversion H3.   destruct H3 eqn:H3'.     invc H3.  simpl in *.  destruct place_terms eqn:pl_t. inversion H3.
        simpl in *. inversion H3. rewrite H.  




    apply IHt with (t_places := places p0 t) (p := p1) (t' := t').
  ++ assumption.
  ++ reflexivity.
  ++ destruct H2. 
  +++ simpl. left. apply H.
  +++ unfold knowsOf_Env in H0. destruct H.
      simpl. right. Print places'.  simpl.      



    unfold knowsOf_Env in H0. destruct (Maps.map_get em p0) eqn:maps; subst; simpl in *.
  ++ destruct H2; simpl in *.
  +++ unfold places in *.  
     apply IHt with (t_places := p1 :: places' t []) (p := p1) (t' := t'); try auto.
  ++++ simpl in *. rewrite H.  reflexivity.
  ++++ simpl. left. auto.
  ++++ inversion H3.
  ++++ apply IHl. simpl in *. inversion H3.   destruct H3 eqn:H3'.     invc H3.  simpl in *.  destruct place_terms eqn:pl_t. inversion H3.
      simpl in *. inversion H3. rewrite H.     
  
  
  invc H3; subst.    





    destruct place_terms eqn:pl_t. inversion H3; subst.
    simpl in *. 
    destruct places' eqn:pl'.
  ++ simpl in *. invc H2.
  +++ specialize IHt with (p := p1) (em := em). apply IHt with (t_places := places p1 t) (p := p1) (t' := t').
  ++++ assumption.
  ++++ reflexivity.
  ++++ simpl. left. auto.
  ++++ simpl. destruct place_terms. inversion pl_t. invc H3. simpl in *.   

  
  destruct pl'.
  
  

    unfold knowsOf_Env in H0. 
    destruct (Maps.map_get em p) eqn:mp. 
    specialize IHt with (p := p0) (em := em). 
    specialize IHt with (t_places := places p0 t) (p := p1) (t' := t').
    
    apply IHt; try assumption; auto.
  ++ destruct places eqn:pl. inversion pl. simpl in *. inversion pl; subst. inversion H2; try (left; assumption).
  inversion H; subst.   destruct t1.    


    destruct t'; subst; simpl in *.    
    unfold knowsOf_Env in H0. (* destruct (Maps.map_get em p0); try (invc H0). *)
    eapply IHt; auto.
  ++ simpl. right. destruct place_terms in H3.
     invc H3. 
  
  
  simpl.  invc H2; subst; try assumption. 
  +++ left. auto.
  +++ invc H; simpl in *.
  ++++ right. destruct place_terms in H3. inversion H3.   simpl. simpl.    invc H0. simpl in *.   invc H. 
  
  left. auto.
  +++ invc H; subst. simpl in *. unfold place_terms.   
  
  
  symmetry.   unfold places. inversion t0.   simpl in *.   subst.  simpl in *.  simpl in *.  
    
    
    
    intros; subst; simpl in *.
    destruct t' eqn:t_dest; simpl in *.
  ++ destruct a.
  +++  split. right.   
    


    specialize IHt with (t_places := (places p0 t)) (p := p1) (t' := t'). apply IHt; try assumption; auto; simpl in *. 
  ++  invc H2; auto. invc H; auto. simpl in *.  invc H3.  right. unfold places'.  cbn in *.      
  
  
  
  subst. simpl in *. unfold place_terms in H3. destruct t.   invc H3.  inversion H2.
  +++ left. rewrite H. auto.
  +++ inversion H.       split.   inversion H2.        
  
  
  specialize IHt with p0 em. simpl in *. unfold distributed_executability in *. intros; subst.   
  
  Restart. 
  
  
  
  intros t; induction t; intros.
  destruct a; ff.
    +
    invc H.
    cbn.
    unfold distributed_executability; intros.
    exists x.
    cbn in *.
    unfold places in *.
    unfold places' in *.
    assert (eqb_plc p p0 = true).
    {
      admit.
    }
    assert (p = p0).
    {
      admit.
    }
    repeat find_rewrite.
    invc H2; try solve_by_inversion.
    split; try reflexivity.
    +
    invc H.
    cbn.
    unfold distributed_executability; intros.
    exists x.
    ff.
    cbn in *.
    unfold places in *.
    unfold places' in *.
    assert (eqb_plc p p0 = true).
    { 
      admit.
    }
    assert (p = p0).
    {
      admit.
    }
    repeat find_rewrite.
    invc H2; try solve_by_inversion.
    split; try reflexivity.
    +
    subst.
    ff.
    unfold distributed_executability; intros.
    cbn in *.
    unfold places in *.
    unfold places' in *.
    assert (eqb_plc p p1 = true).
    {
      admit.
    }
    assert (p = p1).
    {
      admit.
    }
    subst.
    repeat find_rewrite.
    invc H2; try solve_by_inversion.
    unfold canRunAsp_Env in H.
    destruct (Maps.map_get em p1).
    ++
    exists m.
    split; try reflexivity.
    simpl.
    break_let.
    simpl in *.
    split; try eauto.
    cbv.
    trivial.
    ++
    solve_by_inversion.
    +
    invc H.
    cbn.
    unfold distributed_executability; intros.
    exists x.
    cbn in *.
    unfold places in *.
    unfold places' in *.
    assert (eqb_plc p p0 = true).
    {
      admit.
    }
    assert (p = p0).
    {
      admit.
    }
    repeat find_rewrite.
    invc H2; try solve_by_inversion.
    split; try reflexivity.
    +
    invc H.
    cbn.
    unfold distributed_executability; intros.
    exists x.
    cbn in *.
    unfold places in *.
    unfold places' in *.
    assert (eqb_plc p p0 = true).
    {
      admit.
    }
    assert (p = p0).
    {
      admit.
    }
    repeat find_rewrite.
    invc H2; try solve_by_inversion.
    split; try reflexivity.
    +
    invc H.
    cbn.
    unfold distributed_executability; intros.
    exists x.
    cbn in *.
    unfold places in *.
    unfold places' in *.
    assert (eqb_plc p p1 = true).
    {
      admit.
    }
    assert (p = p1).
    {
      admit.
    }
    repeat find_rewrite.
    invc H2; try solve_by_inversion.
    split; try reflexivity.

    - (* at case *)






  (*
  intros. unfold distributed_executability. intros; subst.
  induction t.  
  + simpl in *. destruct a.
  ++ simpl in *.   
  
  
  
  
  
  
  auto. destruct a eqn:H'.
  ++ induction em.
  +++ simpl in *; auto. remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.
      exists m. split.
  ++++ inversion H1.
  +++++ rewrite H0 in H2. pose proof eqb_plc_refl p0. rewrite H3 in H2. inversion H2.    apply eqb_plc_refl in H2.  Search "eqb_plc".     auto.  
  +++ left.    
  remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.

  
  
  inversion H1; simpl in *. 
  
  
  
  
  
  
  inversion H.   remember (build_manifest_helper p0 [] [] [] empty_PolicyT) as m.
     exists m. split.
  +++ simpl in *.      
  
  destruct em eqn:H'.
  ++ split with (x := []).  split with (x := a).
  *)
Abort.