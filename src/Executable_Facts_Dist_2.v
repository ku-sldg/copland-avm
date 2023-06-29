Require Import Term_Defs_Core Manifest Manifest_Generator Manifest_Generator_Facts Executable_Defs_Prop Manifest_Admits Eqb_Evidence.

Require Import StructTactics Auto.

Require Import Coq.Program.Tactics.

Require Import Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


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
    | att p t1 => knowsOf_Env k em p /\ executable_static t1 p em
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
  intros.
  unfold place_terms.
  destruct t'; ff; 
    try auto;
    try (rewrite eqb_plc_refl in *; solve_by_inversion).
Qed.

Lemma app_not_empty : forall A (l1 l2:list A),
l1 ++ l2 <> [] -> 
l1 <> [] \/ l2 <> [].
Proof.
  intros.
  destruct l1; 
  destruct l2.
  -
    ff.
    congruence.
  -
  ff.
  -
  ff.
  left.
  unfold not.
  intros.
  congruence.
  -
    ff.
    left.
    congruence.
    Qed.

    Lemma places'_cumul : forall t p ls,
    In p ls ->
    In p (places' t ls).
    Proof.
      intros.
      generalizeEverythingElse t.
      induction t; intros; 
      try (destruct a);
        ff; eauto.
    Qed.

    Lemma In_dec_tplc : forall (p:Plc) ls,
    In p ls \/ ~ In p ls.
    Proof.
      intros.
      assert ({In p ls} + {~ In p ls}).
      { 
        apply In_dec.
        intros.
        destruct (eq_plc_dec x y); eauto.
      }
      destruct H; eauto.
    Qed. 

    Lemma places_app_cumul : forall p t ls ls',
      In p (places' t ls) -> 
      ~ In p ls ->
      In p (places' t ls').
    Proof.
      intros.
      generalizeEverythingElse t.
      induction t; intros; ff.
      - (* asp case *)
      congruence.
      - (* at case *)
        door.
        +
          eauto.
        +
          eauto.
      - (* lseq case *)

      destruct (In_dec_tplc p (places' t1 ls)).
      +
        assert (In p (places' t1 ls')) by eauto.



        apply places'_cumul.
        eassumption.
      +
      assert (In p (places' t2 ls)) by eauto.
      eapply IHt2.
      eassumption.
      eassumption.
    - (* bseq case *)

    destruct (In_dec_tplc p (places' t1 ls)).
    +
      assert (In p (places' t1 ls')) by eauto.
      apply places'_cumul.
      eassumption.
    +
    assert (In p (places' t2 ls)) by eauto.
    eapply IHt2.
    eassumption.
    eassumption.
  - (* bpar case *)

    destruct (In_dec_tplc p (places' t1 ls)).
    +
      assert (In p (places' t1 ls')) by eauto.



      apply places'_cumul.
      eassumption.
    +
    assert (In p (places' t2 ls)) by eauto.
    eapply IHt2.
    eassumption.
    eassumption.
Qed.

  Lemma places'_cumul' : forall t p ls,
    In p (places' t []) ->
    In p (places' t ls).
    Proof.
      intros.
      generalizeEverythingElse t.
      induction t; intros; 
      try (destruct a);
        try (ff; eauto; ff; congruence).
      - (* lseq case *)
        ff.
        
        assert (In p (places' t2 []) \/ In p (places' t1 [])).
        {
          assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
          { 
              apply In_dec_tplc.
          }
          door.
          +
            eauto.
          +             
            assert (In p (places' t2 [])).
            {
              eapply places_app_cumul.
              apply H.
              eassumption.
            }
            eauto.
        }

        door.
        +
          eauto.
        +
          assert (In p (places' t1 ls)) by eauto.
          apply places'_cumul.
          eauto.

  - (* bseq case *)
          ff.
          
          assert (In p (places' t2 []) \/ In p (places' t1 [])).
          {
            assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
            { 
                apply In_dec_tplc.
            }
            door.
            +
              eauto.
            +             
              assert (In p (places' t2 [])).
              {
                eapply places_app_cumul.
                apply H.
                eassumption.
              }
              eauto.
          }
  
          door.
          +
            eauto.
          +
            assert (In p (places' t1 ls)) by eauto.
            apply places'_cumul.
            eauto.


  - (* bpar case *)
            ff.
            
            assert (In p (places' t2 []) \/ In p (places' t1 [])).
            {
              assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
              { 
                  apply In_dec_tplc.
              }
              door.
              +
                eauto.
              +             
                assert (In p (places' t2 [])).
                {
                  eapply places_app_cumul.
                  apply H.
                  eassumption.
                }
                eauto.
            }
    
            door.
            +
              eauto.
            +
              assert (In p (places' t1 ls)) by eauto.
              apply places'_cumul.
              eauto.
Qed.


Lemma in_plc_term : forall p p0 t,
place_terms t p p0 <> [] ->
In p0 (places p t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
      destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
      destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
- (* at case *)
ff.
destruct (eqb_plc p0 p1) eqn:hi.
+
  left.
  rewrite eqb_eq_plc in *.
  auto.
+
  apply IHt in H.
  door.
  ++
    eauto.
  ++
    eauto.
- (* lseq case *)
ff.
destruct (eqb_plc p p0) eqn:hi.
+
  left.
  rewrite eqb_eq_plc in *.
  auto.
+
  right.

  assert (place_terms t1 p p0 <> [] \/ 
          place_terms t2 p p0 <> []).
          {
            (* Search (_ ++ _ <> []). *)

            apply app_not_empty.
            eassumption.
          }
  door.
  ++
    apply IHt1 in H0.
    assert (In p0 (places' t1 [])).
    {
      assert (p <> p0).
      {
        unfold not.
        intros.
        subst.
        rewrite eqb_plc_refl in *.
        solve_by_inversion.
      }
      door; ff.
      congruence. 
      }

      apply places'_cumul.
      eassumption.
  ++
    apply IHt2 in H0.
    assert (In p0 (places' t2 [])).
    {
      assert (p <> p0).
      {
        unfold not.
        intros.
        subst.
        rewrite eqb_plc_refl in *.
        solve_by_inversion.
      }
      door; ff.
      congruence. 
      }

    
          apply places'_cumul'.
          eauto.

- (* bseq case *)
          ff.
          destruct (eqb_plc p p0) eqn:hi.
          +
            left.
            rewrite eqb_eq_plc in *.
            auto.
          +
            right.
          
            assert (place_terms t1 p p0 <> [] \/ 
                    place_terms t2 p p0 <> []).
                    {
                      (* Search (_ ++ _ <> []). *)
          
                      apply app_not_empty.
                      eassumption.
                    }
            door.
            ++
              apply IHt1 in H0.
              assert (In p0 (places' t1 [])).
              {
                assert (p <> p0).
                {
                  unfold not.
                  intros.
                  subst.
                  rewrite eqb_plc_refl in *.
                  solve_by_inversion.
                }
                door; ff.
                congruence. 
                }
          
                apply places'_cumul.
                eassumption.
            ++
              apply IHt2 in H0.
              assert (In p0 (places' t2 [])).
              {
                assert (p <> p0).
                {
                  unfold not.
                  intros.
                  subst.
                  rewrite eqb_plc_refl in *.
                  solve_by_inversion.
                }
                door; ff.
                congruence. 
                }
          
              
                    apply places'_cumul'.
                    eauto.

- (* bpar case *)
                    ff.
                    destruct (eqb_plc p p0) eqn:hi.
                    +
                      left.
                      rewrite eqb_eq_plc in *.
                      auto.
                    +
                      right.
                    
                      assert (place_terms t1 p p0 <> [] \/ 
                              place_terms t2 p p0 <> []).
                              {
                                (* Search (_ ++ _ <> []). *)
                    
                                apply app_not_empty.
                                eassumption.
                              }
                      door.
                      ++
                        apply IHt1 in H0.
                        assert (In p0 (places' t1 [])).
                        {
                          assert (p <> p0).
                          {
                            unfold not.
                            intros.
                            subst.
                            rewrite eqb_plc_refl in *.
                            solve_by_inversion.
                          }
                          door; ff.
                          congruence. 
                          }
                    
                          apply places'_cumul.
                          eassumption.
                      ++
                        apply IHt2 in H0.
                        assert (In p0 (places' t2 [])).
                        {
                          assert (p <> p0).
                          {
                            unfold not.
                            intros.
                            subst.
                            rewrite eqb_plc_refl in *.
                            solve_by_inversion.
                          }
                          door; ff.
                          congruence. 
                          }
                    
                        
                              apply places'_cumul'.
                              eauto.
Qed.

Lemma in_not_nil : forall A x (ls:list A),
In x ls -> 
ls <> [].
Proof.
  intros.
  destruct ls.
  -
  inversion H.
  -
  congruence.
  Qed.

Lemma dist_exec_lseq : forall p t1 t2 em,
                distributed_executability t1 p em ->
                distributed_executability t2 p em -> 
                distributed_executability (lseq t1 t2) p em.
Proof.
                intros.
                unfold distributed_executability in *; intros.
                destruct_conjs.
                cbn in H2.
                
                destruct (eqb_plc p p0) eqn:hi.
                -
                  invc H2; ff.
                  door.
                  +
                    subst.
                    edestruct H.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.

                    edestruct H0.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.
                    destruct_conjs.
                    assert (x = x0) by congruence.
                    subst.
                    exists x0.
                    split; eauto.
                +
                edestruct H.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.

                    edestruct H0.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.
                    destruct_conjs.
                    assert (x = x0) by congruence.
                    subst.
                    exists x0.
                    split; eauto.
                    rewrite eqb_eq_plc in *.
                    subst.
                    eauto.
                -
                  ff.
                  assert (In t' (place_terms t1 p p0) \/ 
                          In t' (place_terms t2 p p0)).
                  {
                    apply in_app_or.
                    eassumption.
                  }
                
                  door.
                    +

                    apply H.
                    split.
                    right.
                    assert (In p0 (places p t1)).
                      
                   apply in_plc_term.

                  eapply in_not_nil; eauto.
                   unfold places in H4.
                   invc H4.
                   rewrite eqb_plc_refl in *; solve_by_inversion.
                  
                   eassumption.
            
                   eassumption.
                +
                apply H0.
                    split.
                    right.
                    assert (In p0 (places p t2)).
                     
                   apply in_plc_term.

                   eapply in_not_nil; eauto.
                   unfold places in H4.
                   invc H4.
                   rewrite eqb_plc_refl in *; solve_by_inversion.
                  
                   eassumption.
            
                   eassumption.
Qed.

Lemma dist_exec_bseq : forall p t1 t2 em s,
              distributed_executability t1 p em ->
              distributed_executability t2 p em -> 
              distributed_executability (bseq s t1 t2) p em.
              Proof.
                intros.
                unfold distributed_executability in *; intros.
                destruct_conjs.
                cbn in H2.
                
                destruct (eqb_plc p p0) eqn:hi.
                -
                  invc H2; ff.
                  door.
                  +
                    subst.
                    edestruct H.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.

                    edestruct H0.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.
                    destruct_conjs.
                    assert (x = x0) by congruence.
                    subst.
                    exists x0.
                    split; eauto.
                +
                edestruct H.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.

                    edestruct H0.
                    split.
                    left.
                    reflexivity.
                    apply top_plc_refl.
                    destruct_conjs.
                    assert (x = x0) by congruence.
                    subst.
                    exists x0.
                    split; eauto.
                    rewrite eqb_eq_plc in *.
                    subst.
                    eauto.
                -
                  ff.
                  assert (In t' (place_terms t1 p p0) \/ 
                          In t' (place_terms t2 p p0)).
                  {
                    apply in_app_or.
                    eassumption.
                  }
                
                  door.
                    +

                    apply H.
                    split.
                    right.
                    assert (In p0 (places p t1)).
                      
                   apply in_plc_term.

                  eapply in_not_nil; eauto.
                   unfold places in H4.
                   invc H4.
                   rewrite eqb_plc_refl in *; solve_by_inversion.
                  
                   eassumption.
            
                   eassumption.
                +
                apply H0.
                    split.
                    right.
                    assert (In p0 (places p t2)).
                     
                   apply in_plc_term.

                   eapply in_not_nil; eauto.
                   unfold places in H4.
                   invc H4.
                   rewrite eqb_plc_refl in *; solve_by_inversion.
                  
                   eassumption.
            
                   eassumption.
Qed.


Lemma dist_exec_bpar : forall p t1 t2 em s,
            distributed_executability t1 p em ->
            distributed_executability t2 p em -> 
            distributed_executability (bpar s t1 t2) p em.

            Proof.
              intros.
              unfold distributed_executability in *; intros.
              destruct_conjs.
              cbn in H2.
              
              destruct (eqb_plc p p0) eqn:hi.
              -
                invc H2; ff.
                door.
                +
                  subst.
                  edestruct H.
                  split.
                  left.
                  reflexivity.
                  apply top_plc_refl.

                  edestruct H0.
                  split.
                  left.
                  reflexivity.
                  apply top_plc_refl.
                  destruct_conjs.
                  assert (x = x0) by congruence.
                  subst.
                  exists x0.
                  split; eauto.
              +
              edestruct H.
                  split.
                  left.
                  reflexivity.
                  apply top_plc_refl.

                  edestruct H0.
                  split.
                  left.
                  reflexivity.
                  apply top_plc_refl.
                  destruct_conjs.
                  assert (x = x0) by congruence.
                  subst.
                  exists x0.
                  split; eauto.
                  rewrite eqb_eq_plc in *.
                  subst.
                  eauto.
              -
                ff.
                assert (In t' (place_terms t1 p p0) \/ 
                        In t' (place_terms t2 p p0)).
                {
                  apply in_app_or.
                  eassumption.
                }
              
                door.
                  +

                  apply H.
                  split.
                  right.
                  assert (In p0 (places p t1)).
                    
                 apply in_plc_term.

                eapply in_not_nil; eauto.
                 unfold places in H4.
                 invc H4.
                 rewrite eqb_plc_refl in *; solve_by_inversion.
                
                 eassumption.
          
                 eassumption.
              +
              apply H0.
                  split.
                  right.
                  assert (In p0 (places p t2)).
                   
                 apply in_plc_term.

                 eapply in_not_nil; eauto.
                 unfold places in H4.
                 invc H4.
                 rewrite eqb_plc_refl in *; solve_by_inversion.
                
                 eassumption.
          
                 eassumption.
Qed.


(* Proof that the distributed notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_distributed : 
    forall t p em,
      executable_static t p em -> 
      distributed_executability t p em.
Proof.
  intros t.
  dependent induction t; intros.
  - (* asp case *)
    ff.
    destruct a; ff.
    + unfold distributed_executability; intros.
      invc H.
      ff.
      destruct_conjs.
      door; ff; subst.
      exists x.
      split; try eauto.
      door; ff; subst.
      unfold executable.
      trivial.
    + unfold distributed_executability; intros.
      invc H.
      ff.
      destruct_conjs.
      door; ff; subst.
      exists x.
      split; try eauto.
      door; ff; subst.
      unfold executable.
      trivial.
    + unfold distributed_executability; intros.
      subst.
      ff.
      destruct_conjs.
      door; ff; subst.
      unfold canRunAsp_Env in H.
      ff.
      exists m. 
      split; try eauto.
      door; ff.
      rewrite <- H0.
      cbn.
      break_let; ff. subst.
      split; try eassumption.
      cbv.
      trivial.
    + unfold distributed_executability; intros.
      invc H.
      ff.
      destruct_conjs.
      door; ff; subst.
      exists x.
      split; try eauto.
      door; ff; subst.
      unfold executable.
      trivial.
    + unfold distributed_executability; intros.
      invc H.
      ff.
      destruct_conjs.
      door; ff; subst.
      exists x.
      split; try eauto.
      door; ff; subst.
      unfold executable.
      trivial.
    + unfold distributed_executability; intros.
      invc H.
      ff.
      destruct_conjs.
      door; ff; subst.
      exists x.
      split; try eauto.
      door; ff; subst.
      unfold executable.
      trivial.
  - (* at case *)
    simpl in *.
    invc H.
    assert (distributed_executability t p em) by eauto.

    unfold distributed_executability; intros.

    unfold places in *.
    simpl in *.
    destruct_conjs.

    door.
      +
        subst.
        rewrite eqb_plc_refl in *.
        invc H3; ff.
        unfold knowsOf_Env in *; ff.
        exists m. 
        split; try eauto.
      +
        door.
        ++
          subst.
          destruct (eqb_plc p0 p1) eqn:hi.
          +++
            invc H3; ff.
            assert (p0 = p1).
            {
              apply eqb_eq_plc; auto.
            }
            subst. 
            unfold knowsOf_Env in *; ff.
            exists m.
            split; try eauto.
          +++
            unfold distributed_executability in H.
            apply H.
            unfold places.
            split.
            econstructor.
            auto.
            eassumption.
        ++
          subst.
          destruct (eqb_plc p0 p1) eqn:hi.
          +++
            invc H3; ff.
            assert (p0 = p1).
            {
              apply eqb_eq_plc; auto.
            }
            subst. 
            unfold knowsOf_Env in *; ff.
            exists m.
            split; try eauto.
          +++
            unfold distributed_executability in H.
            apply H.
            unfold places.
            split.
            right.
            eassumption.
            eassumption.
  - (* lseq case *)
    invc H.
    assert (distributed_executability t1 p em) by eauto.
    assert (distributed_executability t2 p em) by eauto.

    

    apply dist_exec_lseq; eauto.

  - (* bseq case *)
  invc H.
  assert (distributed_executability t1 p em) by eauto.
  assert (distributed_executability t2 p em) by eauto.

  

  apply dist_exec_bseq; eauto.

  - (* bpar case *) 
  invc H.
  assert (distributed_executability t1 p em) by eauto.
  assert (distributed_executability t2 p em) by eauto.

  apply dist_exec_bpar; eauto.
  Qed.


















(*  (* START:  old proof attempts for static implies distributed executability: *)

  asdf.








    unfold distributed_executability; intros; ff.

    destruct (eqb_plc p p0) eqn: hi.
    +
      invc H4; ff.
      assert (exists m, Maps.map_get em p0 = Some m /\ executable t1 m).
      apply H.
      admit.
      admit.

      assert (exists m, Maps.map_get em p0 = Some m /\ executable t2 m).
      apply H2.
      admit.
      admit.

      destruct_conjs.
      admit.
    +
      door.
      ++
        admit. 
      ++
        unfold distributed_executability in H.
        unfold distributed_executability in H2.


        assert (In t' (place_terms t1 p p0) \/ In t' (place_terms t2 p p0) \/ 
                (In t' (place_terms t1 p p0) /\ In t' (place_terms t2 p p0))).
        { 
          admit. 
        }
        
        assert (In p0 (places p t2) \/ In p0 (places p t1) \/
        (In p0 (places p t2) /\ In p0 (places p t1))).
        {
          admit. 
        }



        door.
        +++
        door.
        ++++
        apply H2.
        eassumption.

        asdffffff.

        



        unfold place_terms in H4.   
      
      
      



        ++
          ff.
          left; eauto.
        ++
          apply top_plc_refl.
        ++
          invc H3.
          assert (exists m, Maps.map_get em p0 = Some m /\ executable t2 m).
          apply H2.
          +++
            ff.
            left; eauto.
          +++
            apply top_plc_refl.
          +++
            invc H3.
            assert (x = x0). 
            {
              destruct_conjs.
              ff.
              repeat find_rewrite.
              ff.
            }

            subst.
            exists x0.
            destruct_conjs.
            split; try eauto.





    door.
      +
        subst.
        rewrite eqb_plc_refl in *.
        invc H4; ff.

        unfold distributed_executability in H.
        unfold distributed_executability in H2.

        specialize H with (p:= p0).
        specialize H2 with (p:= p0).

        assert (exists m, Maps.map_get em p0 = Some m /\ executable t1 m).
        apply H.
          ++
            ff.
            left; eauto.
          ++
            apply top_plc_refl.
          ++
            invc H3.
            assert (exists m, Maps.map_get em p0 = Some m /\ executable t2 m).
            apply H2.
            +++
              ff.
              left; eauto.
            +++
              apply top_plc_refl.
            +++
              invc H3.
              assert (x = x0). 
              {
                destruct_conjs.
                ff.
                repeat find_rewrite.
                ff.
              }

              subst.
              exists x0.
              destruct_conjs.
              split; try eauto.
      +
      unfold distributed_executability in H.
      unfold distributed_executability in H2.

      destruct (eqb_plc p p0) eqn:hi.
      ++
        invc H4; ff.
        assert (exists m, Maps.map_get em p0 = Some m /\ executable t1 m).
        {
          apply H.
          left.
          admit. 
          admit.
        }
        assert (exists m, Maps.map_get em p0 = Some m /\ executable t2 m).
        {
          apply H2.
          left.
          admit. 
          admit.
        }

        destruct_conjs.
        assert (H4 = H5).
        admit.
        subst.
        exists H5. 
        split; try eauto.
      ++
        assert (In t' (place_terms t1 p p0) \/ In t' (place_terms t2 p p0) \/ 
                (In t' (place_terms t1 p p0) /\ In t' (place_terms t2 p p0))).
        { 
          admit. 
        }
        
        assert (In p0 (places p t2) \/ In p0 (places p t1) \/
        (In p0 (places p t2) /\ In p0 (places p t1))).
        {
          admit. 
        }

        door.
        +++
          door.
          ++++






      

      assert (In p0 (places p t1) \/ In p0 (places p t2)).
      admit.
      door.
        ++ 

      assert (In p0 (places' ))




      destruct (eqb_plc p p0).
      ++
      invc H4; ff.

      unfold distributed_executability in H.
      unfold distributed_executability in H2.

      specialize H with (p:= p0).
      specialize H2 with (p:= p0).

      assert (exists m, Maps.map_get em p0 = Some m /\ executable t1 m).
      apply H.
        +++
          ff.
          left; eauto.
        ++
          apply top_plc_refl.
        ++
          invc H3.
          assert (exists m, Maps.map_get em p0 = Some m /\ executable t2 m).
          apply H2.
          +++
            ff.
            left; eauto.
          +++
            apply top_plc_refl.
          +++
            invc H3.
            assert (x = x0). 
            {
              destruct_conjs.
              ff.
              repeat find_rewrite.
              ff.
            }

            subst.
            exists x0.
            destruct_conjs.
            split; try eauto.



          
            





        eexists.

        invc H1.











    assert (executable_static t p em).
    {
      invc H.
      eassumption.
    }
    assert (distributed_executability t p em).
    {
      invc H.
      eapply IHt.
      eassumption. 
    }

    Lemma dist_ex_at : forall t p p0 em,
      distributed_executability t p em ->
      distributed_executability (att p t) p0 em.
      Proof.
        intros.
        unfold distributed_executability in *; intros.
        destruct_conjs.
        ff.
        door.
        -
          subst.
          rewrite eqb_plc_refl in *.
          apply H.
          invc H1; ff.








        apply H.
        split.
        -
        destruct (eqb_plc p1 p) eqn:hi.
        +
          left.
          admit.
        +
          right.
          door.
          ++
          subst.
           

        




        destruct_conjs.
        invc H0.
        invc H1.
        -





        -
          unfold places in *; ff.

          destruct (eqb_plc p1 p) eqn:hi.
            +
              left.
              admit.
            +
              door.
              ++
              subst.
              right.

            
              admit. 



        door.
          - 
            subst.





        Admitted.

    apply dist_ex_at.
    eassumption.





    unfold distributed_executability; intros.
    unfold distributed_executability in IHt.

    unfold place_terms in *; ff.

    door.
    +
      subst.
      destruct (eqb_plc p1 p) eqn:hi.
      ++
        invc H3; ff.
        unfold distributed_executability in H1.
        apply H1.
        admit.
        admit. (* apply top_plc_refl. *)
      ++
      eapply IHt.



      unfold distributed_executability in H1.
      apply H1.
      unfold places.
        unfold place_terms' in H3.



        eapply IHt.
        +++
          eassumption.
        +++


      unfold knowsOf_Env in *; ff.
      unfold distributed_executability in H1.





      exists m. 
      split; try auto. 
      unfold distributed_executability in H1.
      apply H1.
      exists m. 
      split; try eauto.
    + 
      subst.
      door.
      ++
        subst.
        rewrite eqb_plc_refl in *.



    invc H2; ff.








    invc H2; ff.
    +
      rewrite eqb_plc_refl in *; ff.
      door; ff.
      subst.
      unfold executable in *; ff.
      unfold knowsOf_Env in *; ff.
      exists m.
      split; try eauto.
    +
      door.
      ++
        subst.
        rewrite eqb_plc_refl in *.
        destruct (eq_plc_dec p0 p1).
        +++
          subst.
          rewrite eqb_plc_refl in *.
          invc H3; ff.
          unfold knowsOf_Env in *.
          ff.
          exists m. 
          split; try eauto.
        +++
            assert (eqb_plc p0 p1 = false). admit.
            find_rewrite.
            invc H3; ff.
            unfold knowsOf_Env in *.  
            ff.
            unfold distributed_executability in H1.
            eapply H1.
            ++++
            ff.
            left; eauto.
            ++++
            apply top_plc_refl.
      ++
        destruct (eqb_plc p0 p1).
        +++
        invc H3.
        Focus 2.
        solve_by_inversion.

        eapply IHt.
        eassumption.
        right. auto.
        unfold place_terms.



        eapply IHt.
        invc H3; ff.



        invc H3; ff.
        unfold distributed_executability in H1.

        eapply IHt.

        assert (exists m, Maps.map_get em p1 = Some m /\ executable t m).
        apply H1.
        unfold places.
        Manifest_Admits.PolicyT




        unfold executable in H1.
        specialize H1 with (p0:=p1).
        eapply H1.



        eapply IHt.
        +++
         eassumption.
        +++ 
          right. eassumption.
        +++
          destruct (eqb_plc p0 p1).
          ++++
            invc H3; ff. 




          unfold place_terms.
          cbv.
            





          eexists.
          split.
          unfold distributed_executability in H1.

          unfold executable.
          split.  


        ff. 
      
      invc H.






    eapply IHt.
    +
      eassumption.
    +
      unfold places in *; ff.

      door.
      ++
      subst.
      rewrite eqb_plc_refl in *.
      invc H3; ff.


    +
      unfold places in *.
      simpl in *.
      invc H2; ff.

      rewrite eqb_plc_refl in H3.

      admit. 
    + 


    invc H2; ff.
    +
      left; eauto.
    +
      door; ff.
      ++
        left.
        admit.
      ++
        subst.
        right.  







    invc H.
    unfold knowsOf_Env in H0; ff.

    unfold distributed_executability; intros.
    invc H; ff.
    +
      rewrite eqb_plc_refl in H2.
      invc H2; ff.
      exists m. 
      split; try eauto.
    +
      door.
      ++
        subst. 
        rewrite eqb_plc_refl in *.
        simpl in *.
        destruct (eq_plc_dec p0 p1).
        +++
          subst.
          rewrite eqb_plc_refl in *.
          invc H2; ff.
          exists m. 
          split; eauto.
        +++
          assert (eqb_plc p0 p1 = false). admit. 
          find_rewrite.
          invc H2; ff.
          unfold distributed_executability in *.
          eapply IHt with (p:= p0).
          eassumption.
          unfold places.
          exists m. 
          split; try auto  

        




    invc H0.


    Print distributed_executability.
    unfold distributed_executability; intros.
    unfold distributed_executability
    invc H.
    unfold knowsOf_Env in *; ff.
    door; ff; subst.
    +
      door; ff; subst.
      ++
        apply IHt with (p:=p1); try eauto.
        apply top_plc_refl.
      ++
        rewrite eqb_eq_plc in Heqb.
        subst.
        apply IHt with (p:=p); try eauto.
    +
      eapply IHt with (p:=p1).
      ++
        eassumption.
      ++
        left; eauto.
      ++
        assert (p1 <> p).
        { admit. }



      apply top_plc_refl.




      exists m. 
      split; try eassumption.
      unfold distributed_executability in *.




    exists
    invc H2.
















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
       simpl in *. inversion H2. subst.
       unfold knowsOf_Env in H0.
       destruct (Maps.map_get em p0) in H0. simpl in  H0. 
       inversion H0.  
       simpl in *. 
       right. simpl in H2.  
  
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



*)