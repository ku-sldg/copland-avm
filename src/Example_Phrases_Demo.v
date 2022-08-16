Require Import Term_Defs Example_Phrases_Demo_Admits.

Require Import List.
Import ListNotations.

(*
Require Import String.
*)


(*
Definition term1 := att 1 (asp SIG).
*)


Definition create_and_load_ak : Term :=
  asp (
  ASPC ALL COMP (asp_paramsC cal_ak_aspid cal_ak_args source_plc cal_ak_targid)).

Definition pub_key_to_bc : Term :=
  asp (
  ASPC ALL COMP (asp_paramsC pub_bc_aspid pub_bc_args source_plc pub_bc_targid)).

Definition get_data : Term :=
  asp (
  ASPC ALL COMP (asp_paramsC get_data_aspid get_data_args source_plc get_data_targid)).

Definition tpm_sig : Term :=
  asp (
  ASPC ALL EXTD (asp_paramsC tpm_sig_aspid tpm_sig_args source_plc tpm_sig_targid)).

Definition ssl_enc : Term :=
  asp (
  ASPC ALL ENCR (asp_paramsC ssl_enc_aspid ssl_enc_args source_plc ssl_enc_targid)).

Definition demo_phrase : Term :=
  <{ create_and_load_ak ->
     pub_key_to_bc ->
     get_data ->
     tpm_sig ->
     ssl_enc }>.


(*
Definition P0 : Plc := 0.
Definition P1 : Plc := 1.
Definition P2 : Plc := 2.
Definition P3 : Plc := 3.
Definition P4 : Plc := 4.

Definition attest (p:Plc) (targ: TARG_ID) :=
  asp (ASPC (asp_paramsC attest_id [] p targ)).

Definition appraise (p:Plc) (targ: TARG_ID) :=
  asp (ASPC (asp_paramsC appraise_id [] p targ)).

Definition certificate (p:Plc) (targ: TARG_ID) :=
  asp (ASPC (asp_paramsC cert_id [] p targ)).

Definition store (p:Plc) (targ: TARG_ID) :=
  asp (ASPC (asp_paramsC cache_id store_args p targ)).

Definition retrieve (p:Plc) (targ: TARG_ID) :=
  asp (ASPC (asp_paramsC cache_id retrieve_args p targ)).


(* 
pg 29:16 top, Certificate-Style section 
 *)
Definition cert_style_simple_sig : Term :=
  att P1 (lseq
            (attest P1 sys)
            (att 2 (lseq
                      (appraise P2 sys)
                      (asp SIG)))).
       

*)
