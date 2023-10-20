Require Import Term_Defs_Core Params_Admits Manifest (* Executable_Dec *)
               Example_Phrases_Admits Example_Phrases Eqb_Evidence
               Manifest_Generator_Helpers Term_Defs ErrorStMonad_Coq.
               (* Executable_Defs_Prop. *)

Require Import EqClass Maps StructTactics.

Require Import EnvironmentM Manifest_Set.

Require Import Manifest_Union Manifest_Generator Cvm_St Cvm_Impl.

Require Import Manifest ManCompSoundness Manifest_Compiler Manifest_Generator_Facts.

Require Import Manifest_Generator_Union.

Require Import Coq.Program.Tactics.
Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.



Lemma fifi_aspCb : forall m1 m2 amLib params p ev ev' res,
manifest_subset m1 m2 ->
aspCb (manifest_compiler m1 amLib) params p ev ev' = res -> 
aspCb (manifest_compiler m2 amLib) params p ev ev' = res.
Proof.
Admitted.

Lemma fifi_pubKeyCb : forall m1 m2 amLib p res,
manifest_subset m1 m2 -> 
pubKeyCb (manifest_compiler m1 amLib) p = res -> 
pubKeyCb (manifest_compiler m2 amLib) p = res.
Proof.
Admitted.

Lemma fifi_plcCb : forall m1 m2 amLib p res,
manifest_subset m1 m2 -> 
plcCb (manifest_compiler m1 amLib) p = res -> 
plcCb (manifest_compiler m2 amLib) p = res.
Proof.
Admitted.


Lemma man_subset_supports_am : forall m1 m2 amLib,
manifest_subset m1 m2 -> 
supports_am (manifest_compiler m1 amLib) (manifest_compiler m2 amLib).
Proof.
    intros.
    unfold supports_am.
    split; intros.
    -

        eapply fifi_aspCb; eauto.

    -
        split; intros.
        +

        eapply fifi_pubKeyCb; eauto.

        +
            split; intros.
            ++

            eapply fifi_plcCb; eauto.

            ++
            split; intros.

            +++
            eapply fifi_aspCb; eauto.
            +++
            split; intros.

            eapply fifi_pubKeyCb; eauto.
            eapply fifi_plcCb; eauto.
Qed.


Lemma man_subset_lib_supports_man : forall m1 m2 amLib,
manifest_subset m1 m2 -> 
lib_supports_manifest amLib m2 -> 
lib_supports_manifest amLib m1.
Proof.
    intros.
    unfold manifest_subset in *.
    destruct_conjs.
    unfold lib_supports_manifest in *.
    destruct_conjs.

    split; intros; try eauto.

    split; intros; try eauto.

    split; intros; try eauto.
Qed.

Check places.

Print places.
Print places'.


Lemma fofo : forall p' ls absMan,
map_get (mangen_plcTerm_list_union ls) p' = Some absMan -> 
(* In (t,tp) ls -> *)
(
    (*
    forall t', 
    In t' (place_terms t tp p) ->  *)
(
    forall t tp p,
    In (t,tp) ls ->
    In p (places tp t) -> 
    
    exists absMan', 
    map_get (manifest_generator t tp) p = Some absMan' /\
    manifest_subset absMan' absMan)).
Proof.
Admitted.
(*
    intros.
    unfold mangen_plcTerm_list_union in *.
    unfold manifest_generator_plcTerm_list in *.

    assert (
        In  (manifest_generator t tp) (map (fun '(t, p) => manifest_generator t p) ls)

    ).
    {
        admit.
    }
Admitted.
*)

Require Import Auto.

Lemma hehe_last : forall t tp p t' q,
In t' (place_terms t tp p) -> 
In q (places tp t) -> 
In t' (place_terms t tp q).
Proof.
    intros.
    generalizeEverythingElse t.
    induction t; intros.
    -
        ff.
        ff.
        door; try solve_by_inversion; subst.
        door; try solve_by_inversion; subst.
        rewrite eqb_plc_refl in Heqb.
        solve_by_inversion.
    -
    ff.
    asdf.
        unfold place_terms in *.


        unfold places in H0.
        invc H0.
        + admit. 
        +
            ff.
            door; try solve_by_inversion; subst.

            ++
            break_if.
            +++
            rewrite eqb_eq_plc in Heqb; subst.
            break_if.
            ++++
            eassumption.
            ++++
            specialize IHt with ()





        ff.

            rewrite eqb_plc_refl.

            break_if; eauto.
            ++
            eauto.
            ++

            specialize IHt with (tp:=p0)(p:=q)(t':=t')(q:=q).
            apply IHt in H.



            left.
            break_if.
            ++
            eassumption.
            ++
            specialize IHt with (tp:=p) (p:=p0) (t':=t')(q:=p).
            apply IHt in H.
            +++
            ff.
            left.

Admitted.





Theorem mangen_compiler_soundness_distributed_list' : forall t tp p absMan amLib amConf ls, 
    In (t,tp) ls -> 

    map_get (mangen_plcTerm_list_union ls) p = Some absMan ->
    lib_supports_manifest amLib absMan ->
    manifest_compiler absMan amLib = amConf ->
    forall st,
  
    (*
    st.(st_AM_config) = amConf ->
    *)

    (supports_am amConf (st.(st_AM_config))) -> 

  
      (  forall t', 
           In t' (place_terms t tp p) -> 
          (exists st', 
          
          build_cvm (copland_compile t') st = (resultC tt, st')) \/
          
          (exists st' errStr,
          build_cvm (copland_compile t') st = (errC (dispatch_error (Runtime errStr)), st'))
      ).
  Proof.
    intros.

    assert (exists pp, In pp (places tp t)).
    {
        exists tp.
        unfold places.
        simpl.
        eauto.
    }
    destruct_conjs.

    pose (fofo p ls absMan H0 t tp H5 H H6).

    destruct_conjs.


assert (lib_supports_manifest amLib e) as HH.
{
    eapply man_subset_lib_supports_man.
    2: {
        eapply H1.
    }
    eassumption.
}


    eapply manifest_generator_compiler_soundness_distributed' with (amLib := amLib) (absMan := e).

    3: {
        reflexivity.
    }

    eassumption.

    eassumption.

    eapply supports_am_trans.

    2 : {
        eassumption.
    }

    rewrite <- H2.

    eapply man_subset_supports_am; eauto.

    eapply hehe_last; eauto.

Qed.




Theorem mangen_compiler_soundness_distributed_list : forall t tp p absMan amLib amConf ls, 
    In (t,tp) ls -> 



    map_get (mangen_plcTerm_list_union ls) p = Some absMan ->
    lib_supports_manifest amLib absMan ->
    manifest_compiler absMan amLib = amConf ->
    forall st,

    st.(st_AM_config) = amConf ->

    (*
    (supports_am amConf (st.(st_AM_config))) ->
    *) 

  
      (  forall t', 
           In t' (place_terms t tp p) -> 
          (exists st', 
          
          build_cvm (copland_compile t') st = (resultC tt, st')) \/
          
          (exists st' errStr,
          build_cvm (copland_compile t') st = (errC (dispatch_error (Runtime errStr)), st'))
      ).
  Proof.
    intros.
    eapply mangen_compiler_soundness_distributed_list'; eauto.
    rewrite H3.
    eapply supports_am_refl.
Qed.






    (*

    admit.

    2: {
        eassumption.
    }

    reflexivity.



    apply H5.

    edestruct fofo. 
    eassumption.

    5: {
        eassumption.
    }

    Lemma 



    2: {
        eassumption.
    }
    2: {
        eassumption.
    }
    2: {
        eassumption.
    }
    2: {
        eassumption.
    }

    unfold mangen_plcTerm_list_union in *.
    unfold manifest_generator_plcTerm_list in *.

    assert (
        In (manifest_generator t tp) 
        (map (fun '(t, p) => manifest_generator t p) ls)
    ).
    {
        admit.
    }


    Lemma hoho : forall (env:EnvironmentM) envs f e x v,
        In env envs ->
        map_get 
            (fold_right f e envs) x = Some v ->
        map_get env x = Some v.
    Proof.
    Admitted.

    eapply hoho; eauto.
    intros.


    *)



    (*
    manifest_generator_compiler_soundness_distributed t tp p absMan amLib amConf.
    (mangen_plcTerm_list_union ls)
    *)