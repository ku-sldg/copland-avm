(* Example phrases.  Some of these are inspired by the 
    Copland "Flexible Mechanisms" work:  https://dl.acm.org/doi/10.1145/3470535 *)


Require Import Term_Defs Example_Phrases_Admits Example_Phrases_Demo_Admits.

Require Import Example_Phrases_Pre_Admits.

Require Import List.
Import ListNotations.


Definition attest (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC attest_id [] p targ)).

Definition appraise (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC appraise_id [] p targ)).

Definition attest1 (p:Plc) (targ: TARG_ID) :=
    asp (ASPC ALL EXTD (asp_paramsC attest1_id [] p targ)).

Definition attest2 (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC attest2_id [] p targ)).

(*
Definition appraise_inline (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC appraise_inline_id [] p targ)).
*)

Definition certificate (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC cert_id [] p targ)).

Definition store (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC cache_id store_args p targ)).

Definition retrieve (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC cache_id retrieve_args p targ)).


(* 
pg 29:16 top, Certificate-Style section 
 *)
Definition cert_style_simple_sig : Term :=
  att P1 (lseq
            (attest P1 sys)
            (att P2 (lseq
                      (appraise P2 sys)
                      (asp SIG)))).

(* 
pg 29:15, Certificate-Style section 
 *)  
Definition cert_style : Term :=
  att P1 (lseq
           (attest P1 sys)
           (att P2 (lseq
                    (appraise P2 sys)
                    (certificate P2 sys)))).

(* 
pg. 29:16 bottom, Certificate-Style section
*)
Definition cert_cache_p1 : Term :=
  lseq
    (attest P1 sys)
    (lseq
       (att P2
            (lseq
               (appraise P2 sys)
               (certificate P2 sys)))
       (store P1 cache)).

Definition cert_cache_p0 : Term :=
  att P1
      (lseq
         (bseq (NONE,ALL)
               (retrieve P1 cache)
               (asp CPY))
         (asp SIG)).

(* 
pg. 29:17, Background Check section 
 *)
Definition bg_check : Term :=
  lseq
    (att P1 (attest P1 sys))
    (att P2 (appraise P2 sys)).


(*
pg. 29:18, Parallel Mutual Attestation section
TODO:  Do subscripts of attest and appraise in text necessitate special ASP args?
*)
Definition par_mut_p0 : Term :=
  lseq
    (att P1 (attest P1 sys))
    (att P2 (appraise P2 sys)).
  
Definition par_mut_p1 : Term :=
  lseq
    (att P0 (attest P0 sys))
    (att P2 (appraise P2 sys)).


(*
pg. 29:19, Layered Background Check section
 *)

Definition layered_bg' : Term :=
  lseq
    (attest P1 sys)
    (lseq
       (attest P3 att_tid)
       (attest P4 att_tid)).

Definition layered_bg''' : Term :=
  bpar (ALL,ALL)
       (att P3 (attest P3 sys))
       (att P4 (attest P4 sys)).

Definition layered_bg'' : Term :=
        bseq (ALL,ALL)
             (att P3 (attest P3 sys))
             (att P4 (attest P4 sys)).

Definition layered_bg_weak : Term :=
  att P1
      (lseq
         (bpar (ALL,ALL)
               layered_bg'
               layered_bg'')
         (att P2
              (lseq
                 (appraise P2 it)
                 (asp SIG)))).
         
Fixpoint cop_phrase_depth (t : Term) : nat :=
  match t with
  | (asp _) => 1
  | (att _ t') => cop_phrase_depth t'
  | (lseq t1 t2) => 1 + max (cop_phrase_depth t1) (cop_phrase_depth t2)
  | (bseq _ t1 t2) => 1 + max (cop_phrase_depth t1) (cop_phrase_depth t2)
  | (bpar _ t1 t2) => 1 + max (cop_phrase_depth t1) (cop_phrase_depth t2)
  end.

(*
pg. 29:20, Layered Background Check section 
 *)
Definition layered_bg_strong : Term :=
    att P1
      (lseq
         (bseq (ALL,ALL) (* only change from layered_bg_weak on this line (bpar --> bseq) *)
               layered_bg'
               layered_bg'')
         (att P2
              (lseq
                 (appraise P2 it)
                 (asp SIG)))).


(*
Definition attest : ASP_ID. Admitted.
*)


(*
Definition attest1 : ASP_ID. Admitted.
Definition attest2 : ASP_ID. Admitted.
*)



(*
Definition appraise : ASP_ID. Admitted.
Definition certificate : ASP_ID. Admitted.
Definition sys : TARG_ID. Admitted.
Require Import Manifest_Admits.
Definition BASE_ADDR : ASP_Address. Admitted.
*)


(*
Definition cert_style : Term :=
  att P1 (lseq
           (attest P1 sys)
           (att P2 (lseq
                    (appraise P2 sys)
                    (certificate P2 sys)))).

*)

Open Scope cop_ent_scope.

(* This should be identical to cert_style above (modulo Coq notations...) *)
Definition example_phrase_basic : Term := 
  <{
    @ P1 [
      (<< attest_id P1 sys >>) -> 
      @ P2 [
        << appraise_id P2 sys >> ->
        << cert_id P2 sys >>
      ]
    ]
  }>.

Example example_basic_eq_cert_style : 
  example_phrase_basic = cert_style.
Proof.
  reflexivity.
Qed.

Definition appraise_inline_asp_with_args (p:Plc) (targ: TARG_ID) (args:ASP_ARGS) : Term := 
  asp (ASPC ALL EXTD (asp_paramsC appraise_inline_id args p targ)).


Definition sub1 : Term := 
  <{ << attest1_id P1 sys >> +<+ << attest2_id P1 sys >> }>.

Definition sub2 : Term := 
  <{ << cert_id P2 sys >> }>.

Definition example_phrase : Term := 
    att P1 (
      lseq 
        sub1 
        (
          att P2 
            (
              lseq 
                (appraise_inline_asp_with_args P2 sys appraise_inline_args)
                sub2
            )
        )).


Definition example_phrase_orig : Term := 
  <{
    @ P1 [
      (<< attest1_id P1 sys >> +<+ << attest2_id P1 sys >>) -> 
      @ P2 [
        << appraise_inline_id P2 sys >> ->
        << cert_id P2 sys >>
      ]
    ]
  }>.

Example test_ex_phrase : example_phrase = example_phrase_orig.
Proof.
intros.
cbv.
Abort.

(*
Definition example_phrase_p2_appraise : Term := 
  <{
    @ P1 [
      (<< attest1_id P1 sys >> +<+ << attest2_id P1 sys >>) ] 
  }>.
*)


(*

Definition check_ssl_sig_args : ASP_ARGS.
Admitted.

Definition example_phrase : Term := 
  <{
    @ P1 [
      (<< attest1_id P1 sys >> +<+ << attest2_id P1 sys >>) -> 
      @ P2 [
        \t3< appraise_inline_asp_with_args P2 sys appraise_inlines_args > ->
        << cert_id P2 sys >>
      ]
    ]
  }>.

*)

Definition appinlinet := appraise_inline_asp_with_args P0 sys check_ssl_sig_args.

Definition inline_auth_phrase : Term := 
  <{
    (<< ssl_sig_aspid P0 sys >>) -> 

    @ P1 [
      appinlinet
      (* \t3< appraise_inline_asp_with_args P0 sys check_ssl_sig_args > *) ->
      (* (<< check_ssl_sig_aspid P0 sys >>)  ->  *)
      (<< attest_id P1 sys >>) -> 
      @ P2 [
        << appraise_id P2 sys >> ->
        << cert_id P2 sys >>
      ]
    ]
  }>.

Close Scope cop_ent_scope.

