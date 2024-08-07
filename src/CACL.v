Require Import Term_Defs Maps ID_Type.

Require Import List.
Import ListNotations.


Inductive CACL_Permission := 
| CACL_Read    : CACL_Permission 
| CACL_Write   : CACL_Permission
| CACL_Invoke  : CACL_Permission.

Definition CACL_Access : Type := (ID_Type * CACL_Permission).
Definition CACL_Policy : Type := MapC ID_Type (list CACL_Access).


Open Scope string_scope.

Definition empty_CACL_Policy := [("", (nil:(list CACL_Access)))].



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

Definition CACL_policy_union (p1:CACL_Policy) (p2:CACL_Policy) : CACL_Policy.
Admitted.

Definition CACL_policy_generator_ASP (a:ASP) (p:Plc) : CACL_Policy := 
    match a with 
    | SIG =>   [(p, [(sig_id, CACL_Invoke)])] 
    | HSH =>   [(p, [(hsh_id, CACL_Invoke)])] 
    | ENC _ => [(p, [(enc_id, CACL_Invoke)])] 
    | ASPC _ _ (asp_paramsC aid _ targp targid) => 
        [(p, [(aid, CACL_Invoke)]);
         (aid, [(targid, CACL_Read)])]
    | _ => empty_CACL_Policy 
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

