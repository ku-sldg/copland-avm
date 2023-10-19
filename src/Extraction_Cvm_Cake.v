Require Extraction.

Require Import Term_Defs Term_Defs_Core Cvm_Run IO_Stubs AM_Monad Cvm_Monad.
(* Require Import CopParser. *)

Require Import Example_Phrases Example_Phrases_Demo.

Require Import Manifest_Generator Manifest_Compiler.

Require Import Server_AM Client_AM_Local.


Require Import List.
Import ListNotations.

Extraction Language CakeML. (* OCaml. *) 

(*
Unset Extraction Optimize.
*)

Extract Inductive nat => "nat" ["O" "S"].
Extract Inductive bool => "bool" ["True" "False"].
Extract Inductive option => "option" ["Some" "None"].

Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
(*Extract Inductive prod => "( * )" [ "" ]. *)

(*
Extraction Implicit do_asp [3 4].
Extraction Implicit do_asp' [3 4]. 
*)
Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].


Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".
(* Extract Constant + => "add". *)
(* Extract Constant Nat.add => "(+)". *)

Definition P0 : Plc. Admitted.
Definition P1 : Plc. Admitted.
Definition P2 : Plc. Admitted. 
Definition attest1 : ASP_ID. Admitted.
Definition attest2 : ASP_ID. Admitted.
Definition appraise : ASP_ID. Admitted.
Definition certificate : ASP_ID. Admitted.
Definition sys : TARG_ID. Admitted.
Require Import Manifest_Admits.
Definition BASE_ADDR : ASP_Address. Admitted.

Definition example_phrase : Term := 
  <{
    @ P1 [
      (<< attest1 P1 sys >> +<+ << attest2 P1 sys >>) -> 
      @ P2 [
        << appraise P1 sys >> ->
        << certificate P1 sys >>
      ]
    ]
  }>.

Require Import Maps StringT ErrorStMonad_Coq.
Definition ERR_STR : StringT. Admitted.

Definition AM_LIB : AM_Library := {|
  ASPServer_Cb        := fun addr => fun _ => fun _ => fun _ => fun _ => errC (messageLift ERR_STR) ;
  PubKeyServer_Cb     := fun addr => fun _ => errC (Runtime ERR_STR) ;
  PlcServer_Cb        := fun addr => fun _ => errC (Runtime ERR_STR) ;
  UUIDServer_Cb       := fun addr => fun _ => errC (Runtime ERR_STR) ;

  (* Server Addresses *)
  ASPServer_Addr    := BASE_ADDR ; 
  PubKeyServer_Addr := BASE_ADDR ; 
  PlcServer_Addr    := BASE_ADDR ;
  UUIDServer_Addr   := BASE_ADDR ;

  (* Local Mappings *)
  Local_ASPS        := [
      (attest1, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs)) ;
      (attest2, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs)) ;
      (appraise, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs)) ;
      (certificate, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs))
    ];
  Local_Appraisal_ASPS := [];

  Local_Plcs        := [];
  Local_PubKeys     := [];
|}.

Example compute_man_gens : 
  exists m, map_get (manifest_generator example_phrase P0) P2 = Some m ->
  exists ac,
    manifest_compiler m AM_LIB = ac.
Proof.
  assert (EqClass.eqb P0 P0 = true) by admit;
  assert (EqClass.eqb P0 P1 = false) by admit;
  assert (EqClass.eqb P0 P2 = false) by admit;
  assert (EqClass.eqb P1 P0 = false) by admit;
  assert (EqClass.eqb P1 P1 = true) by admit;
  assert (EqClass.eqb P1 P2 = false) by admit;
  assert (EqClass.eqb P2 P0 = false) by admit;
  assert (EqClass.eqb P2 P1 = false) by admit;
  assert (EqClass.eqb P2 P2 = true) by admit.
  unfold example_phrase, manifest_generator, manifest_generator',
    asp_manifest_generator, at_manifest_generator, manifest_update_env, 
    asp_manifest_update, aspid_manifest_update, update_manifest_policy_targ,
    knowsof_manifest_update.
  simpl in *.
  repeat (
    try rewrite H in *;
    try rewrite H0 in *;
    try rewrite H1 in *;
    try rewrite H2 in *;
    try rewrite H3 in *;
    try rewrite H4 in *;
    try rewrite H5 in *;
    try rewrite H6 in *;
    try rewrite H7 in *;
    simpl in *).
  assert (EqClass.eqb certificate appraise = false). admit.
  repeat rewrite H8 in *.
  assert (EqClass.eqb attest2 attest1 = false). admit.
  repeat rewrite H9 in *.
  eexists; intros HM; inversion HM.
  clear HM H11.
  repeat unfold manifest_compiler, generate_Plc_dispatcher, generate_PubKey_dispatcher, 
    generate_UUID_dispatcher, generate_ASP_dispatcher, generate_appraisal_ASP_dispatcher,
    generate_appraisal_ASP_dispatcher', generate_ASP_dispatcher'.
  simpl in *.
  unfold in_dec_set.

  simpl in *.
  destruct eqb.



(*
Extract Constant get_ev => "bind get (fn st => ret (st_ev st)) : cvm_st -> coq_EvC".
(* "st <- (@get cvm_st CVM_Error) ;; ret (st_ev st)". *)

*)

(*
  bind get (fn st =>
    let val ac = let val Coq_mkAM_St _ _ amConfig = st in amConfig end in
    (case decrypt_bs_to_rawev bs params ac of
       Coq_errC e => failm (Coq_dispatch_error e)
     | Coq_resultC r =>
       (case check_et_size et r of
          Coq_errC e => failm (Coq_dispatch_error e)
        | Coq_resultC _ => ret r)) end)
		*)

Definition term_list : list Term := 
	[cert_style; cert_style_test; cert_style_trimmed; cert_cache_p1; cert_cache_p0; cert_cache_p0_trimmed].

Separate Extraction run_cvm manifest_compiler  
		    run_am_app_comp 
			handle_AM_request (* am_client_auth am_client_gen *)
			term_list ssl_sig_parameterized kim_meas
		    par_mut_p0 par_mut_p1 layered_bg_strong cm_meas
		    man_gen_run_attify empty_am_result
        am_client_gen_local
        run_am_app_comp.
