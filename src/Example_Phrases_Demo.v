Require Import Term_Defs Example_Phrases_Demo_Admits Example_Phrases_Pre_Admits AbstractedTypes.

Require Import List.
Import ListNotations.


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


Definition ssl_sig_parameterized (p:Plc) : Term :=
  asp (
      ASPC ALL EXTD (asp_paramsC ssl_sig_aspid ssl_sig_args p ssl_sig_targid)).

Definition client_data_phrase : Term :=
  asp (
      ASPC ALL KILL (asp_paramsC store_clientData_aspid store_clientData_args source_plc store_clientData_targid)).



Definition cm_meas (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC cm_aspid cm_args p targ)).
