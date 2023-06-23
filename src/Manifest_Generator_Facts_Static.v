Require Import Maps Term_Defs_Core Manifest Eqb_Evidence
Executable_Facts_Map
  Manifest_Generator Executable_Defs_Prop.

Require Import Auto.

Require Import StructTactics.

Require Import List.
Import ListNotations.


Theorem manifest_generator_executability_static :
    forall (t:Term) (p:Plc), 
        executable_static t p (manifest_generator t p).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
    destruct a; 
    try (simpl in *; trivial).
    +
      destruct a.
      cbv.
      ff.
      assert (eqb p p = true).
      {
        admit.
      }
      find_rewrite.
      solve_by_inversion.
  - (* at case *)

    unfold manifest_generator in *.
    cbn.
    intros.
    unfold knowsOf_Env in *.
    ff.
    Focus 2.
    admit.
    split.
    +
    ff.
    unfold e_empty in *.
    unfold map_set in *.
    ff.
    assert (m = {|
      my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
      asps := [];
      uuidPlcs := [p];
      pubKeyPlcs := [];
      policy := Manifest_Admits.empty_PolicyT
    |}).
    admit.
    subst.
    simpl.
    left. eauto.
    +
    assert (executable_static t p (manifest_generator' p t e_empty)).
    { eauto. }



    assert ()
    -

    unfold map_get in *.
    ff. 

    assert (executable_static t p0 (manifest_generator' p0 t e_empty)).
    { eauto. }


    split.
    +







    Focus 2. admit.
    intros.
    unfold manifest_generator in IHt.
    unfold e_empty in *.
    ff.
    Check map_set.
    Locate map_set.
    unfold executable_static.
    fold manifest_generator.


    cbn.
    ff.
    cbv.
    ff.

      simpl in *.
      trivial.


Abort.




(*
Theorem manifest_generator_executability :
    forall (t t':Term) (top_plc p:Plc) (t_places : list Plc) 
           (env_map : EnvironmentM) (m:Manifest), 
    env_map = (manifest_generator t top_plc) ->
    t_places = (places top_plc t) ->
    In p t_places -> 
    In t' (place_terms t top_plc p) ->
    Maps.map_get env_map p = Some m ->
    executable t' m.
*)