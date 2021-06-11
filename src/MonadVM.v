(*
Definition of the CVM Monad + monadic helper functions.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term ConcreteEvidence GenStMonad Axioms_Io.
Require Import Maps StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Export StVM.



Definition CVM := St cvm_st.

(* VM monad operations *)

Definition put_ev (e:EvidenceC) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let p' := st_pl st in
     let et := st_evT st in 
     put (mk_st e et tr' p').

Definition put_evT (et:Evidence) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let p' := st_pl st in
     let e := st_ev st in 
     put (mk_st e et tr' p').

Definition put_pl (p:Plc) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let e' := st_ev st in
     let et := st_evT st in
     put (mk_st e' et tr' p).

Definition get_ev : CVM EvidenceC :=
  st <- get ;;
  ret (st_ev st).

Definition get_evT : CVM Evidence :=
  st <- get ;;
  ret (st_evT st).

Definition get_pl : CVM Plc :=
  st <- get ;;
  ret (st_pl st).

Definition modify_evm (f:EvidenceC -> EvidenceC) : CVM unit :=
  st <- get ;;
  let '{| st_ev := e; st_evT := et; st_trace := tr; st_pl := p |} := st in
  put (mk_st (f e) et tr p).

Definition add_trace (tr':list Ev) : cvm_st -> cvm_st :=
  fun '{| st_ev := e; st_evT := et; st_trace := tr; st_pl := p |} =>
    mk_st e et (tr ++ tr') p.

Definition add_tracem (tr:list Ev) : CVM unit :=
  modify (add_trace tr).

Definition split_ev (i:nat) (sp:Split) (e:EvidenceC) (p:Plc) :
  CVM (EvidenceC*Evidence) :=
  et <- get_evT ;;
  let '(e1,et1) := splitEv_l sp e et in
  let '(e2,et2) := splitEv_r sp e et in
  put_ev e1 ;;
  put_evT et1 ;;
  add_tracem [Term_Defs.split i p] ;;
  ret (e2,et2).

Locate splitEv_l.

(*
Definition split_ev_par (i:nat) (sp1 sp2:SP) (*((*loc_e1*) loc_e2:Loc) *)
           (*(t1 t2:AnnoTerm)*) (e:EvidenceC) (p:Plc) : CVM EvidenceC :=
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    (*let loc_e1 := fst (range t1) in
    let loc_e2 := fst (range t2) in *)
    (*put_store_at loc_e1 e1 ;; *)
    (*put_store_at loc_e2 e2 ;; *)
    add_tracem [Term_Defs.split i p] ;;
    ret e1.
*)


(** * Partially-symbolic implementations of IO operations *)

Definition invokeUSM (x:nat) (i:ASP_ID) (l:list Arg) (tpl:Plc) (tid:TARG_ID) : CVM EvidenceC :=
  e <- get_ev ;;
  et <- get_evT ;;
  p <- get_pl ;;
  put_evT (uu i l tpl tid et) ;;
  add_tracem [umeas x p i l tpl tid];;
  ret (uuc i l tpl tid x e).

Definition encodeEv (e:EvidenceC) : BS.
Admitted.

Definition signEv (x:nat) : CVM EvidenceC :=
  e <- get_ev ;;
  et <- get_evT ;;
  p <- get_pl ;;
  put_evT (gg p et) ;;
  add_tracem [sign x p] ;;  (* TODO: evidence type for sign event? *)
  ret (ggc p x e).

Definition hashEvC (e:EvidenceC): BS.
Admitted.

Definition hashEv (x:nat) : CVM EvidenceC :=
  e <- get_ev ;;
  et <- get_evT ;;
  p <- get_pl ;;
  put_evT (hh p et) ;;
  add_tracem [hash x p et] ;;  (* TODO: evidence type for hash event? *)
  ret (hhc p (hashEvC e)).

Definition copyEv (x:nat) : CVM EvidenceC :=
  p <- get_pl ;;
  add_tracem [copy x p] ;;
  get_ev.

Definition do_prim (x:nat) (a:ASP) : CVM EvidenceC :=
  match a with
  | CPY => copyEv x
  | ASPC asp_id l tpl tid =>
    invokeUSM x asp_id l tpl tid         
  | SIG =>
    signEv x
  | HSH =>
    (*
    e <- get_ev ;;
    p <- get_pl ;; *)
    hashEv x
  end.

Definition sendReq (t:AnnoTerm) (q:Plc) (reqi:nat) : CVM unit :=
  p <- get_pl ;;
  et <- get_evT ;;
  add_tracem [req reqi p q (unanno t) et].

(* Primitive CVM Monad operations that require IO Axioms *)
Definition doRemote (t:AnnoTerm) (q:Plc) (e:EvidenceC) : CVM EvidenceC :=
  add_tracem (remote_events t q) ;;
  ret (toRemote t q e).

Definition receiveResp (t:AnnoTerm) (q:Plc) (rpyi:nat) : CVM EvidenceC :=
  p <- get_pl ;;
  e <- get_ev ;;
  et <- get_evT ;;
  e' <- doRemote t q e ;;
  put_evT (aeval t q et) ;;
  add_tracem [rpy (Nat.pred rpyi) p q] ;;
  ret e'. 

Definition join_seq (n:nat) (p:Plc) (e1:EvidenceC) (e1t:Evidence) (e2:EvidenceC) (e2t:Evidence) : CVM unit :=
  put_ev (ssc e1 e2) ;;
  put_evT (ss e1t e2t);;
  add_tracem [join n p].

Definition join_par (n:nat) (p:Plc) (e1:EvidenceC) (e1t:Evidence) (e2:EvidenceC) (e2t:Evidence) : CVM unit :=
  put_ev (ppc e1 e2) ;;
  put_evT (pp e1t e2t) ;;
  add_tracem [join n p].
   
Ltac monad_unfold :=
  repeat unfold
  execSt,  
  do_prim,
  invokeUSM,
  signEv,
  hashEv,
  copyEv,

  sendReq,
  doRemote,
  receiveResp,
  (*runParThreads, 
  runParThread, *)

  get_ev,
  get_pl,
  get_evT,
  add_tracem,
  modify_evm,
  (*split_ev_seq,
  join_par, *)
  add_trace,
  failm,
  get,
  when,
  put,
  nop,
  modify,
  bind,
  ret in *;
  simpl in *.


Ltac vmsts :=
  simpl in *;
  repeat
    match goal with
    | [H: cvm_st |- _] => destruct H
    end.

Ltac amsts :=
  repeat match goal with
         | H:cvm_st |- _ => destruct H
         end.

Ltac pairs :=
  simpl in *;
  vmsts;
  repeat
    match goal with
    | [H: (Some _, _) =
          (Some _, _) |- _ ] => invc H; monad_unfold
                                                          
    | [H: {| st_ev := _; st_trace := _; st_pl := _(*; st_store := _*) |} =
          {| st_ev := _; st_trace := _; st_pl := _ (*; st_store := _*) |} |- _ ] =>
      invc H; monad_unfold
    end; destruct_conjs; monad_unfold.

(*
Definition eval_asp (a:ASP) (e:EvidenceC) : EvidenceC :=
  match a with
  | CPY => e 
  | ASPC i _ =>
    let bs := 0 in (* TODO: must bs be hardcoded? *)
    (uuc i bs e)
  | SIG =>
    let bs := 0 in
    (ggc bs e)
(*  | HSH =>
    let bs := 0 in
    (hhc bs e) *)
  end.



Fixpoint eval (t:Term) (* (p:Plc) *) (e:EvidenceC) : EvidenceC :=
  match t with
  | asp a => eval_asp a e
  | att q t1 => toRemote t1 e
  | lseq t1 t2 =>
    let e1 := eval t1 e in
    eval t2 e1
         
  (*| bseq (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := eval t1 e1 in
    let e2' := eval t2 e2 in
    (ssc e1' e2') 
  | bpar (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := parallel_eval_thread t1 e1 in
    let e2' := parallel_eval_thread t2 e2 in
    (ppc e1' e2') *)
  end.

Axiom remote_eval : forall e annt,
    eval annt e = toRemote annt e.

Axiom para_eval_thread: forall e annt,
    parallel_eval_thread annt e = eval annt e.


Inductive evalR: Term -> EvidenceC -> EvidenceC -> Prop :=
| mttc: forall e, evalR (asp CPY) e e
| uutc: forall i args e,
    evalR (asp (ASPC i args)) e (uuc i (0) e)
| ggtc: forall e,
    evalR (asp SIG) e (ggc 0 e)
(*| hhtc: forall e,
    evalR (asp HSH) e (hhc 0 e)  *)
| atc: forall q t' e e',
    evalR t' e e' ->
    evalR (att q t') e e'
| lseqc: forall t1 t2 e e' e'',
    evalR t1 e e' ->
    evalR t2 e' e'' ->
    evalR (lseq t1 t2) e e''
(*| bseqc: forall t1 t2 sp1 sp2 e e1 e2,
    evalR t1 (splitEv sp1 e) e1 ->
    evalR t2 (splitEv sp2 e) e2 ->
    evalR (bseq (sp1,sp2) t1 t2) e (ssc e1 e2)
| bparc: forall t1 t2 sp1 sp2 e e1 e2,
    evalR t1 (splitEv sp1 e) e1 ->
    evalR t2 (splitEv sp2 e) e2 ->
    evalR (bpar (sp1,sp2) t1 t2) e (ppc e1 e2) *).



Lemma eval_iff_evalR: forall t e e',
    evalR t e e' <-> eval t e = e'.
Proof.
    split.
  - (* -> case *)
    intros.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros.

    + destruct a; try (inv H; reflexivity).
    + inv H. simpl.
      rewrite <- remote_eval.
      eauto.
    + inv H.
      assert (eval t1 e = e'0).
      eauto.
      subst.
      simpl.
      eauto.
      (*
    + inv H.
      assert (eval t1 (splitEv sp1 e) = e1) by eauto.
      assert (eval t2 (splitEv sp2 e) = e2) by eauto.
      simpl.
      destruct sp1; destruct sp2;
        simpl; subst; eauto.
    + inv H.
      assert (eval t1 (splitEv sp1 e) = e1) by eauto.
      assert (eval t2 (splitEv sp2 e) = e2) by eauto.
      simpl.
      repeat rewrite para_eval_thread in *.
      destruct sp1; destruct sp2;
        simpl; subst; eauto. *)
  - (* <- case *)
    intros.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros.
    + inv H.
      destruct a; try econstructor.
    + inv H.
      simpl.
      econstructor.
      rewrite <- remote_eval.
      eauto.
    + econstructor; eauto.
      (*
    + destruct s.
      simpl in H.
      destruct s; destruct s0; simpl in *; subst;
        econstructor; (try simpl); eauto; try (econstructor).
    + destruct s.
      simpl in H.
      repeat rewrite para_eval_thread in *.
      destruct s; destruct s0; simpl in *; subst;
        econstructor; (try simpl); eauto; try (econstructor) . *)
Defined.
*)




(* *** Deprecated Parallel helper functions *** *)

(*
Definition runParThread (t:AnnoTerm) (p:Plc) (loc1:Loc) (loc2:Loc) :
  CVM unit (*(list Ev)*) :=
  e <- get_store_at loc1 ;;
  put_ev e ;;
  copland_compile t ;;
  e' <- get_ev ;;
  

  (*
  let el := parallel_vm_events t p in
  let e' := parallel_vm_thread t p e in
  (*let loc := fst (range t) in *)
   *)
  
  put_store_at loc2 e' (* ;;
  ret el*) .

Definition runParThreads (t1 t2:AnnoTerm) (p:Plc) (loc_e1 loc_e1' loc_e2 loc_e2':Loc) : CVM unit :=
  el1 <- runParThread t1 p loc_e1 loc_e1' ;;
  el2 <- runParThread t2 p loc_e2 loc_e2' ;;
  add_tracem (shuffled_events el1 el2).

 *)
