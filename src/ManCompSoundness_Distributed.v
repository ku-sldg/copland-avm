Require Import Manifest Manifest_Compiler Manifest_Generator AbstractedTypes
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics Cvm_Monad EqClass Manifest_Admits.
Require Import Manifest_Generator_Facts Executable_Defs_Prop Executable_Facts_Dist.

Require Import ManCompSoundness.

Require Import Coq.Program.Tactics.

Require Import Auto.
Import ListNotations.





Theorem manifest_generator_compiler_soundness_distributed : forall t tp p absMan amLib amConf,
  map_get (manifest_generator t tp) p = Some absMan ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  forall st,
    (* Note, this should be trivial typically as amConf = st.(st_AM_config) and refl works *)
    supports_am amConf (st.(st_AM_config)) ->  

    (  forall t', 
         In t' (place_terms t tp p) -> 
         st.(st_pl) = p -> 
        
         exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st') \/
        build_cvm (copland_compile t') st = (errC (dispatch_error Runtime), st')
    ).
Proof.
Abort.






(*
Lemma dist_exec_implies_cvm_exec : forall t tp e p absMan amLib amConf,
    distributed_executability t tp e -> 
    map_get e p = Some absMan -> 
    lib_supports_manifest amLib absMan -> 
    manifest_compiler absMan amLib = amConf -> 

    forall st,
    (* Note, this should be trivial typically as amConf = st.(st_AM_config) and refl works *)
    supports_am amConf (st.(st_AM_config)) ->  

    (  forall t', 
         In t' (place_terms t tp p) -> 
         st.(st_pl) = p ->
        
         exists st', 
        build_cvm (copland_compile t') st = (resultC tt, st') \/
        build_cvm (copland_compile t') st = (errC (dispatch_error Runtime), st')
    ).
Proof.
    intros.
    unfold distributed_executability in H.
    specialize H with (p:=p) (t':=t').
    assert (exists m, map_get e p = Some m /\ executable_local t' m).
    {
        eapply H.
        split.
        -
            admit.
        -
            eassumption.

    }
    destruct_conjs.
    clear H.
    find_rewrite.
    ff.

    generalizeEverythingElse t.
    induction t; intros.

    - (* asp case *)

    destruct a.
    + (* null case *)
    unfold place_terms in *.
    ff.
    door; try solve_by_inversion.
    subst.
    unfold executable_local in H8.

    eexists.
    left.
    ff.
    reflexivity.

    + (* cpy case *)
    unfold place_terms in *.
    ff.
    door; try solve_by_inversion.
    subst.
    unfold executable_local in H8.

    eexists.
    left.
    ff.
    reflexivity.

    + (* ASPC case *)
    unfold place_terms in *.
    ff.
    door; try solve_by_inversion.
    subst.
    unfold executable_local in H8.

    destruct a.
    unfold canRunAsp_Manifest in *.
    ff.
    subst.

        destruct s.
        ++
            ff.
            ff.
            +++
            eexists.
            right.
            destruct d.
            ++++

            unfold supports_am in *.
            destruct_conjs.

            unfold lib_supports_manifest in *.

            destruct_conjs.
            simpl in *.

            find_apply_hyp_hyp.
            destruct_conjs.

            unfold aspCb in *.
            break_match.

            (*
            Heqr2: aspCb (asp_paramsC a l p t) (st_pl st) (encodeEvRaw (get_bits (st_ev st)))
          (get_bits (st_ev st)) = errC Unavailable
            *)

            assert (
                aspCb (asp_paramsC a l p t) (st_pl st) (encodeEvRaw (get_bits (st_ev st)))
                (get_bits (st_ev st)) = errC Runtime).

            {
                eapply e3.
                break_match.
                +
                break_match.
                ++
                break_match.
                eauto.
                ++
                admit.
            +
                assert (aspCb = c).
                unfold aspCb in *.
                destruct c; try solve_by_inversion.
                invc Heqr.
                destruct c; eauto.
                admit.
                admit.
                destruct c.
                ff.
                ff.
                ff.
                ff.
                specialize e0 with (aid:=a) (l:=l) (targ:=p) (targid:=t) (p':=(st_pl st)) (ev := (encodeEvRaw (get_bits (st_ev st)))) (ev' := []) (res:= (encodeEvRaw (get_bits (st_ev st)))).
                eapply e0.

                admit.
            }
            congruence.



            break_match.

            ff.



            ff.



            admit.
            ++++
            eauto.
            +++
            eauto.
        ++
            ff.
            ff.
            +++
            eexists.
            right.
            destruct d.
            ++++
            admit.
            ++++
            eauto.
    + (* SIG case *)





        2: {
            eauto.
        }

        destruct d.
        +++
        eexists.
        left.
        eauto.
        right.
        eauto.

    eexists.

    left.

    destruct s.
    ++
    ff.
    ff.
    +++
    unfold supports_am in *.
    destruct_conjs.
    ff.


    repeat ff.
    break_let.
    df.
    ff.

    eexists.
    left.
    ff.
    reflexivity.



        admit.
    ++
        solve_by_inversion.



    assert ()
Admitted.

*)
