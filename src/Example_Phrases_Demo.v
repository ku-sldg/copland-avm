Require Import Term_Defs Example_Phrases_Demo_Admits AbstractedTypes.

(*
Require Import String.
 *)

Require Import List.
Import ListNotations.




(*
Definition kim_meas : Term :=
  <{ << kim_meas_aspid dest_plc kim_meas_targid >> }>.
 *)


Definition kim_meas (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC kim_meas_aspid kim_meas_args p targ)).

Definition create_and_load_ak : Term :=
  asp (
      ASPC ALL KEEP
           (asp_paramsC
              cal_ak_aspid cal_ak_args source_plc cal_ak_targid)).

Definition pub_key_to_bc : Term :=
  asp (
      ASPC ALL KEEP
           (asp_paramsC
              pub_bc_aspid pub_bc_args source_plc pub_bc_targid)).

Definition get_data : Term :=
  <{ << get_data_aspid source_plc get_data_targid >> }>.

Definition tpm_sig : Term :=
  <{ << tpm_sig_aspid source_plc tpm_sig_targid >> }>.

Definition ssl_enc : Term :=
  asp (
      ASPC ALL ENCR
           (asp_paramsC
              ssl_enc_aspid ssl_enc_args source_plc ssl_enc_targid)).


(*
Definition demo_phrase : Term :=
  <{ kim_meas ->
     create_and_load_ak ->
     pub_key_to_bc ->
     get_data ->
     tpm_sig ->
     ssl_enc }>.



Open Scope cop_ent_scope.

Definition demo_phrase2 : Term :=
  <{ @ demo_plc_2 [kim_meas] }>.

Definition demo_phrase3 : Term :=
  <{ @ demo_plc_2 [kim_meas -> @ demo_plc_1 [kim_meas]] }>.
*)

Definition ssl_sig_parameterized (p:Plc) : Term :=
  asp (
      ASPC ALL EXTD (asp_paramsC ssl_sig_aspid ssl_sig_args p ssl_sig_targid)).


(*
Definition ssl_sig : Term :=
  asp (
      ASPC ALL EXTD (asp_paramsC ssl_sig_aspid ssl_sig_args dest_plc ssl_sig_targid)).
*)

Definition client_data_phrase : Term :=
  asp (
      ASPC ALL KILL (asp_paramsC store_clientData_aspid store_clientData_args source_plc store_clientData_targid)).



(*
Definition etsize_mt_sig :=
  et_size (uu 0 EXTD sig_params mt).

Compute etsize_mt_sig.
*)

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
