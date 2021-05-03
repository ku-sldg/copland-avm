(*
Definition of the AM Monad + monadic helper functions.

Author:  Adam Petz, ampetz@ku.edu
*)
Require Import Maps GenStMonad Impl_vm StVM StAM.
Require Import Term ConcreteEvidence (*VmSemantics*) (*MonadVM*).

Require Import List.
Import ListNotations.

(*
Definition Policy := nat.

Record AM_Env : Type := mkAM_Env
                          { myPolicy : Policy}.

Definition init_env := (mkAM_Env 0).
 *)

Definition AM := St AM_St.

Definition am_newNonce (bs :BS) : AM EvidenceC :=
  (*let myPol := asks myPolicy in *)
  am_st <- get ;;
  let mm := am_nonceMap am_st in
  let i := am_nonceId am_st in
  let appm := st_aspmap am_st in
  let sigm := st_sigmap am_st in
  let checkedm := checked am_st in
  (*let plm := am_pl am_st in *)            
  let newMap := map_set mm i bs in
  let newId := i + 1 in
  put (mkAM_St newMap newId appm sigm checkedm (*plm*)) ;;         
  ret (nnc i bs mtc).

Definition getNonceVal (nid:nat) : AM BS :=
  m <- gets am_nonceMap ;;
  let maybeVal := map_get m nid in
  match maybeVal with
  | Some bs => ret bs
  | None => failm
  end.

Locate Nat.eq_dec.
Require Import PeanoNat.

Definition add_checked (nid:nat) : AM unit :=
  am_st <- get ;;
  let mm := am_nonceMap am_st in
  let i := am_nonceId am_st in
  let appm := st_aspmap am_st in
  let sigm := st_sigmap am_st in
  let checkedm := checked am_st in
  put (mkAM_St mm i appm sigm (checkedm ++ [nid])).
  

Definition am_checkNonce (nid:nat) (bs:BS) : AM BS :=
  good_bs <- getNonceVal nid ;;
  add_checked nid ;;
  if (Nat.eq_dec bs good_bs) then ret 1 else ret 0.

Definition nonces_checked (nm:MapC nat BS) (l:list nat) : Prop :=
  forall x, 
  (exists v, bound_to nm x v) ->
  In x l.

Definition nonces_checked_st (st:AM_St) : Prop :=
  match st with
  | mkAM_St nm i am sm l =>
    nonces_checked nm l
  end.
    
  
  

Definition runAM {A:Type} (k:(AM A)) (* (env:AM_Env) *) (st:AM_St) : (option A) * AM_St :=
  runSt k st.

Definition incNonce := runAM (am_newNonce 42) empty_amst.
(*
Compute (incNonce).
*)

(*
Definition am_run_t (t:Term) (e:EvidenceC) : AM EvidenceC :=
  let annt := annotated t in
  let start_st := mk_st e [] 0 [] in
  ret (st_ev (run_cvm annt start_st)).
*)

(*
Definition t1 := (att 1 (lseq (asp (ASPC 44 [])) (asp SIG))).
Definition t2 := (lseq (asp (ASPC 44 [])) (asp SIG)).
*)

(*
Compute (am_run_t t2 mtc empty_amst).
*)

(*
Definition am_proto_1 :=
  n2 <- am_newNonce 42 ;;
    n <- am_newNonce 43 ;;
    am_run_t t2 n.
*)

(*
Compute (runAM am_proto_1 empty_amst).
*)

(*
Fixpoint nonces (e:EvidenceC) (l:list nat) : list nat :=
  match e with
  | nnc i _ e' => nonces e' ([i] ++ l)
  | _ => l
  end.
 *)

(** * Helper functions for Appraisal *)

Definition am_get_app_asp (p:Plc) (i:ASP_ID) : AM ASP_ID :=
  m <- gets st_aspmap ;;
  let maybeId := map_get m (p,i) in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

Definition am_get_sig_asp (p:Plc) : AM ASP_ID :=
  m <- gets st_sigmap ;;
  let maybeId := map_get m p in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

    





