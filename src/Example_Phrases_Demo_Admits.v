Require Import Term_Defs.

Require Import List.
Import ListNotations.

(*
Require Import String.

Definition term1 := att 1 (asp SIG).
 *)

(*
Definition source_plc : Plc := O.
Definition target_plc : Plc := S O.
 *)

Definition client_data_bs : BS. Admitted.


Definition source_plc : Plc. Admitted.
Definition dest_plc : Plc. Admitted.

Definition cal_ak_targid : ASP_ID. Admitted.
Definition cal_ak_aspid : ASP_ID. Admitted.
Definition cal_ak_args : list Arg. Admitted.

Definition pub_bc_targid : ASP_ID. Admitted.
Definition pub_bc_aspid : ASP_ID. Admitted.
Definition pub_bc_args : list Arg. Admitted.

Definition get_data_targid : ASP_ID. Admitted.
Definition get_data_aspid : ASP_ID. Admitted.
Definition get_data_args : list Arg. Admitted.

Definition tpm_sig_targid : ASP_ID. Admitted.
Definition tpm_sig_aspid : ASP_ID. Admitted.
Definition tpm_sig_args : list Arg. Admitted.

Definition ssl_enc_targid : ASP_ID. Admitted.
Definition ssl_enc_aspid : ASP_ID. Admitted.
Definition ssl_enc_args : list Arg. Admitted.

Definition store_clientData_targid : ASP_ID. Admitted.
Definition store_clientData_aspid : ASP_ID. Admitted.
Definition store_clientData_args : list Arg. Admitted.

Definition ssl_sig_targid : ASP_ID. Admitted.
Definition ssl_sig_aspid : ASP_ID. Admitted.
Definition ssl_sig_args : list Arg. Admitted.


Definition kim_meas_targid : ASP_ID. Admitted.
Definition kim_meas_aspid : ASP_ID. Admitted.
Definition kim_meas_args : list Arg. Admitted.


(*
Definition cal_ak_targid : ASP_ID := "" % string.
Definition cal_ak_aspid : ASP_ID := "cal_ak_id" % string.
Definition cal_ak_args : list Arg := ["pub.bin" %string; "handle.txt" %string].

Definition pub_bc_targid : ASP_ID := "" % string.
Definition pub_bc_aspid : ASP_ID := "pub_bc_id" % string.
Definition pub_bc_args : list Arg := ["pub.bin" %string].

Definition get_data_targid : ASP_ID := "" % string.
Definition get_data_aspid : ASP_ID := "get_data_id" % string.
Definition get_data_args : list Arg := ["data.txt" %string].

Definition tpm_sig_targid : ASP_ID := "" % string.
Definition tpm_sig_aspid : ASP_ID := "tpm_sig_id" % string.
Definition tpm_sig_args : list Arg := ["handle.txt" %string].

Definition ssl_enc_targid : ASP_ID := "" % string.
Definition ssl_enc_aspid : ASP_ID := "ssl_enc_id" % string.
Definition ssl_enc_args : list Arg := ["targ_pub.bin" %string].

*)
