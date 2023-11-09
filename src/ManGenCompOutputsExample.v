Require Import Example_Phrases_Admits Example_Phrases.

Require Import Manifest_Admits Manifest BS.

Require Import Maps StringT ErrorStMonad_Coq.

Require Import Manifest_Generator Manifest_Compiler.

Require Import List.
Import ListNotations.


(*
Definition P0 : Plc. Admitted.
Definition P1 : Plc. Admitted.
Definition P2 : Plc. Admitted. 
Definition attest : ASP_ID. Admitted.
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
       << appraise P2 sys >> ->
       << certificate P2 sys >>
     ]
   ]
  }>.
*)


Definition BASE_ADDR : ASP_Address. Admitted.

Definition passed_bs : BS. Admitted.

Definition ERR_STR : StringT. Admitted.
Definition P0_UUID : UUID. Admitted.
Definition P1_UUID : UUID. Admitted.
Definition P2_UUID : UUID. Admitted.
Definition P3_UUID : UUID. Admitted.


Definition AM_LIB : AM_Library := {|
  ASPServer_Cb        := fun addr => fun _ => fun _ => fun _ => fun _ => errC (messageLift ERR_STR) ;
  PubKeyServer_Cb     := fun addr => fun _ => errC (Runtime ERR_STR) ;
  PlcServer_Cb        := fun addr => fun _ => errC (Runtime ERR_STR) ;
  UUIDServer_Cb       := fun addr => fun _ => errC (Runtime ERR_STR) ;

  UUID_AM_Clone := P3_UUID ; 

  (* Server Addresses *)
  ASPServer_Addr    := BASE_ADDR ; 
  PubKeyServer_Addr := BASE_ADDR ; 
  PlcServer_Addr    := BASE_ADDR ;
  UUIDServer_Addr   := BASE_ADDR ;
  (* Local Mappings *)
  Local_ASPS        := [
     (attest_id, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs)) ;
     (attest1_id, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs)) ;
     (attest2_id, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs)) ;
     (appraise_id, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs)) ;
     (cert_id, (fun _ => fun _ => fun _ => fun _ => resultC passed_bs))
   ];
  Local_Appraisal_ASPS := [];
  Local_Plcs        := [
   (P0, P0_UUID) ;
   (P1, P1_UUID);
   (P2, P2_UUID)
  ];
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
   simpl in * ).
  assert (EqClass.eqb cert_id appraise_id = false). admit.
  repeat rewrite H8 in *.
  assert (EqClass.eqb attest2_id attest1_id = false). admit.
  repeat rewrite H9 in *.
  eexists; intros HM; inversion HM.
  clear HM H11.
  repeat unfold manifest_compiler, generate_Plc_dispatcher, generate_PubKey_dispatcher, 
   generate_UUID_dispatcher, generate_ASP_dispatcher, generate_appraisal_ASP_dispatcher,
   generate_appraisal_ASP_dispatcher', generate_ASP_dispatcher'.
  simpl in *.
  assert (appraise_id <> attest1_id) by admit;
  assert (appraise_id <> attest2_id) by admit;
  assert (appraise_id <> cert_id) by admit;
  assert (cert_id <> attest1_id) by admit;
  assert (cert_id <> attest2_id) by admit;
  assert (attest1_id <> attest2_id) by admit.
  repeat destruct EqClass.EqClass_impl_DecEq;
  try congruence.
  unfold in_dec_set.
  simpl in *.