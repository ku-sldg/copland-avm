Require Import Term_Defs Maps ID_Type EqClass.

Require Import Manifest_Set.

Require Import List.
Import ListNotations.


Inductive CACL_Permission := 
| CACL_Read    : CACL_Permission 
| CACL_Write   : CACL_Permission
| CACL_Invoke  : CACL_Permission.

Definition eqb_CACL_Permission (a1 a2 : CACL_Permission)  : bool := 
    match a1 with 
    | CACL_Read => 
        match a2 with 
        | CACL_Read => true 
        | _ => false 
        end 
    | CACL_Write => 
        match a2 with 
        | CACL_Write => true 
        | _ => false 
        end 
    | CACL_Invoke => 
        match a2 with 
        | CACL_Invoke => true 
        | _ => false 
        end
    end.

(** Admitted Lemmas relating boolean to propositional equality for 
    CACL_Permission *)
Lemma eqb_eq_CACL_Permission: forall i1 i2,
    eqb_CACL_Permission i1 i2 = true <-> i1 = i2.
Proof.
    split;
        intros;
        destruct i1; destruct i2; 
        unfold eqb_CACL_Permission in *;
        try congruence;
        try eauto.
Qed.

Global Instance EqClassCACL_Permission `{H : EqClass ID_Type} : EqClass CACL_Permission := {
  eqb := eqb_CACL_Permission ;
  eqb_eq := eqb_eq_CACL_Permission
}.

Definition CACL_Access : Type := (ID_Type * CACL_Permission).
Definition CACL_Policy : Type := MapC ID_Type (list CACL_Access).


Definition eqb_CACL_Access `{H : EqClass ID_Type} (a1 a2 : CACL_Access)  : bool := 
    eqbPair a1 a2.

(** Admitted Lemmas relating boolean to propositional equality for 
   ASP ID and PARAMS *)
Lemma eqb_eq_CACL_Access: forall `{H : EqClass ID_Type} i1 i2,
    eqb_CACL_Access i1 i2 = true <-> i1 = i2.
Proof.
    split.
    -
        intros.
        unfold eqb_CACL_Access in *.
        eapply pair_eqb_eq; eauto.
    -
        intros.
        unfold eqb_CACL_Access in *.
        eapply pair_eqb_eq; eauto.
Qed.

Global Instance EqClassCACL_Access `{H : EqClass ID_Type} : EqClass CACL_Access := {
  eqb := eqb_CACL_Access ;
  eqb_eq := eqb_eq_CACL_Access
}.

Definition CACL_Access_list_union (l1:list CACL_Access) (l2:list CACL_Access) : list CACL_Access := 
    manset_union (list_to_manset l1) l2.

Lemma nodup_CACL_Access_list_union: forall l1 l2, 
    NoDup (CACL_Access_list_union l1 l2).
Proof.
    intros.
    eapply nodup_manset_union.
    eapply nodup_list_to_manset.
Qed.

Definition update_CACL_Policy (i:ID_Type) (ls:list CACL_Access) (m:CACL_Policy) : CACL_Policy := 
    match (map_get m i) with 
    | Some ls' => map_set m i (CACL_Access_list_union ls ls')
    | _ => map_set m i (list_to_manset ls)
    end.

(*
Definition environment_union'' (p:Plc) (m1:Manifest) (e2:EnvironmentM) : EnvironmentM := 
  match (map_get e2 p) with 
  | Some m2 => 
    let new_man := manifest_union_asps m2 m1 in  (* m2 first here to preserve plc *)
      map_set e2 p new_man 
  | None => map_set e2 p m1
  end.

                                      (*  B  *)            (*  A  *)        (*  A  *)
Definition env_union_helper (e1_pr:(Plc*Manifest)) (e2:EnvironmentM) : EnvironmentM := 
  environment_union'' (fst e1_pr) (snd e1_pr) e2.

Definition environment_union (e1:EnvironmentM) (e2:EnvironmentM) : EnvironmentM :=
  fold_right env_union_helper e2 e1.

*)

Definition CACL_policy_union'' (p:ID_Type) (ls:list CACL_Access) (e2:CACL_Policy) : CACL_Policy := 
    match (map_get e2 p) with 
    | Some ls' => 
      let new_man := CACL_Access_list_union ls ls' in  (* m2 first here to preserve plc *)
        map_set e2 p new_man 
    | None => map_set e2 p ls
    end.


                                                    (*  B  *)            (*  A  *)        (*  A  *)
Definition CACL_policy_union_helper (pr:(ID_Type*(list CACL_Access))) (e2:CACL_Policy) : CACL_Policy := 
    CACL_policy_union'' (fst pr) (snd pr) e2.



Definition CACL_policy_union (p1:CACL_Policy) (p2:CACL_Policy) : CACL_Policy := 
    fold_right CACL_policy_union_helper p2 p1.


Open Scope string_scope.

Definition default_CACL_Policy := [("", (nil:(list CACL_Access)))].



(* Plcs *)
Definition P0 : Plc := "P0".
Definition P1 : Plc := "P1".
Definition P2 : Plc := "P2".
Definition P3 : Plc := "P3".
Definition P4 : Plc := "P4".

(* ASP IDs *)
Definition attest_id : ASP_ID := "attest_id".
Definition appraise_id : ASP_ID := "appraise_id".
Definition certificate_id : ASP_ID := "certificate_id".
Definition hashfile_id : ASP_ID := "hashfile_id".
Definition sig_id : ASP_ID := "sig_id".
Definition hsh_id : ASP_ID := "hsh_id".
Definition enc_id : ASP_ID := "enc_id".

(* TARG IDs *)
Definition sys_targ : TARG_ID := "sys_targ".
Definition att_targ : TARG_ID := "att_targ".
Definition it_targ : TARG_ID := "it_targ".
Definition hashfile_targ : TARG_ID := "hashfile_targ".

(*
(* AM TARG IDs *)
Definition AM_P0 : TARG_ID := "AM0".
Definition AM_P1 : TARG_ID := "AM1". 
Definition AM_P2 : TARG_ID := "AM2". 
*)

Close Scope string_scope.

Definition certificate_style : Term :=
  att P1 (
    lseq 
      (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P1 sys_targ)))
      (att P2 (
        lseq 
          (asp (ASPC ALL (EXTD 1) (asp_paramsC appraise_id [] P2 sys_targ)))
          (asp (ASPC ALL (EXTD 1) (asp_paramsC certificate_id [] P2 sys_targ)))
      ))
  ).

Definition example_cacl_policy : CACL_Policy := 
    [(P1, [(attest_id, CACL_Invoke)]);
     (P2, [(appraise_id, CACL_Invoke);
           (certificate_id, CACL_Invoke)]);
     (attest_id, [(sys_targ, CACL_Read)])
     ].


(*
Eval compute  in (CACL_policy_union example_cacl_policy example_cacl_policy).
*)

Definition test_cacl_compute := (CACL_policy_union example_cacl_policy example_cacl_policy).







Definition CACL_policy_generator_ASP (a:ASP) (p:Plc) : CACL_Policy := 
    match a with 
    | SIG =>   [(p, [(sig_id, CACL_Invoke)])] 
    | HSH =>   [(p, [(hsh_id, CACL_Invoke)])] 
    | ENC _ => [(p, [(enc_id, CACL_Invoke)])] 
    | ASPC _ _ (asp_paramsC aid _ targp targid) => 
        [(p, [(aid, CACL_Invoke)]);
         (aid, [(targid, CACL_Read)])]
    | _ => default_CACL_Policy 
    end.


Fixpoint CACL_policy_generator (t:Term) (p:Plc) (pol:CACL_Policy) : CACL_Policy := 
    match t with 
    | asp a => CACL_policy_union pol (CACL_policy_generator_ASP a p)
    | att q t' => (CACL_policy_generator t' q pol)
    | lseq t1 t2 => 
        (CACL_policy_generator t2 p (CACL_policy_generator t1 p pol))
    | bseq _ t1 t2 => 
        (CACL_policy_generator t2 p (CACL_policy_generator t1 p pol))
    | bpar _ t1 t2 => 
        (CACL_policy_generator t2 p (CACL_policy_generator t1 p pol))
    end.

