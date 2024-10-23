Require Import Term_Defs_Core CACL_Defs CACL_Typeclasses.
Require Import Maps Manifest_Set ID_Type.

Require Import List.
Import ListNotations.

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
    match (map_get i m) with 
    | Some ls' => map_set i (CACL_Access_list_union ls ls') m
    | _ => map_set i (list_to_manset ls) m
    end.

Definition CACL_policy_union'' (p:ID_Type) (ls:list CACL_Access) (e2:CACL_Policy) : CACL_Policy := 
    match (map_get p e2) with 
    | Some ls' => 
      let new_man := CACL_Access_list_union ls ls' in  (* m2 first here to preserve plc *)
        map_set p new_man e2 
    | None => map_set p ls e2 
    end.

                                                    (*  B  *)            (*  A  *)        (*  A  *)
Definition CACL_policy_union_helper (pr:(ID_Type*(list CACL_Access))) (e2:CACL_Policy) : CACL_Policy := 
    CACL_policy_union'' (fst pr) (snd pr) e2.

Definition CACL_policy_union (p1:CACL_Policy) (p2:CACL_Policy) : CACL_Policy := 
    fold_right CACL_policy_union_helper p2 p1.


Open Scope string_scope.

Definition default_CACL_Policy := [("", (nil:(list CACL_Access)))].

Definition sig_id : ASP_ID := "sig_id".
Definition hsh_id : ASP_ID := "hsh_id".
Definition enc_id : ASP_ID := "enc_id".

Definition CACL_policy_generator_ASP (a:ASP) (p:Plc) : CACL_Policy := 
    match a with 
    | SIG =>   [(p, [(sig_id, CACL_Invoke)])] 
    | HSH =>   [(p, [(hsh_id, CACL_Invoke)])] 
    | ENC _ => [(p, [(enc_id, CACL_Invoke)])] 
    | ASPC (asp_paramsC aid _ targp targid) => 
        [(p, [(aid, CACL_Invoke)]);
         ((append p (append ", " aid)), [(targid, CACL_Read)])]
    | _ => default_CACL_Policy 
    end.

Close Scope string_scope.


Fixpoint CACL_policy_generator' (t:Term) (p:Plc) (pol:CACL_Policy) : CACL_Policy := 
    match t with 
    | asp a => CACL_policy_union pol (CACL_policy_generator_ASP a p)
    | att q t' => (CACL_policy_generator' t' q pol)
    | lseq t1 t2 => 
        (CACL_policy_generator' t2 p (CACL_policy_generator' t1 p pol))
    | bseq _ t1 t2 => 
        (CACL_policy_generator' t2 p (CACL_policy_generator' t1 p pol))
    | bpar _ t1 t2 => 
        (CACL_policy_generator' t2 p (CACL_policy_generator' t1 p pol))
    end.

Definition CACL_policy_generator (t:Term) (p:Plc) : CACL_Policy := 
  CACL_policy_generator' t p [].