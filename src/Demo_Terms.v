Require Import Term_Defs JSON.

Require Import String.
Require Import List.
Import ListNotations.

Definition gen_asp (asp_id:ASP_ID) (args:ASP_ARGS)
                   (targPlc:Plc) (targId:TARG_ID) : Term := 
    asp (ASPC (asp_paramsC 
                asp_id 
                args 
                targPlc
                targId)).

Definition appr_term : Term := (asp APPR).

Open Scope string_scope.
Definition gather_file_contents : ASP_ID := "readfile".
Definition hash_file_contents : ASP_ID := "hashfile".
Definition hash_dir_contents : ASP_ID := "hashdir".
Definition hash_evidence : ASP_ID := "hashevidence".
Definition provision : ASP_ID := "provision".
Close Scope string_scope.

Definition gather_targ_asp (targPlc:Plc) (targId:TARG_ID) (args:ASP_ARGS) : Term := 
    gen_asp 
        gather_file_contents 
        args targPlc targId.

Definition hash_targ_asp (targPlc:Plc) (targId:TARG_ID) (args:ASP_ARGS) : Term := 
    gen_asp 
        hash_file_contents 
        args targPlc targId.

Definition hash_dir_asp (targPlc:Plc) (targId:TARG_ID) (args:ASP_ARGS) : Term := 
    gen_asp 
        hash_dir_contents 
        args targPlc targId.

Definition provision_targ_asp (targPlc:Plc) (targId:TARG_ID) (args:ASP_ARGS) : Term := 
    gen_asp 
        provision 
        args targPlc targId.

Definition hash_evidence_asp (targPlc:Plc) (targId:TARG_ID) (args:ASP_ARGS) : Term := 
    gen_asp 
        hash_evidence 
        args targPlc targId.