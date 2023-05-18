Require Import Term_Defs Example_Phrases_Admits.

Require Import List.
Import ListNotations.

(* Definition term1 := att 1 (asp SIG). *)


Definition attest (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC attest_id [] p targ)).

Definition appraise (p:Plc) (targ: TARG_ID) :=
  asp (ASPC ALL EXTD (asp_paramsC appraise_id [] p targ)).

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

Definition layered_bg'' : Term :=
  bpar (ALL,ALL)
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
  



Definition test_par_nested : Term :=
  bpar (ALL,ALL)
       (asp SIG)
       (bpar (ALL,ALL)
             (asp SIG)
             (asp SIG)).
       
