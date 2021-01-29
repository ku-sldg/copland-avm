(*
Definition of the CVM Monad + monadic helper functions.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term ConcreteEvidence GenStMonad Axioms_Io.
Require Import Maps StructTactics.

Require Import List.
Import ListNotations.

Require Export StVM.

Definition CVM := St cvm_st.


(* VM monad operations *)

Definition put_store_at (n:nat) (e:EvidenceC) : CVM unit :=
  st <- get ;;
     let e' := st_ev st in
     let tr' := st_trace st in
     let p' := st_pl st in
     let store' := st_store st in
  (*let '{| st_ev := _; st_stack := s; st_trace := tr |} := st in*)
     put (mk_st e' tr' p' (map_set store' n e)).

Definition get_store_at (n:nat) : CVM EvidenceC :=
  st <- get ;;
     let store' := st_store st in
     let maybeEv := map_get store' n in
     match maybeEv with
     | Some e => ret e
     | None => failm
     end.

Definition put_ev (e:EvidenceC) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let p' := st_pl st in
     let store' := st_store st in
  (*let '{| st_ev := _; st_stack := s; st_trace := tr |} := st in*)
    put (mk_st e tr' p' store').

Definition get_ev : CVM EvidenceC :=
  st <- get ;;
  ret (st_ev st).

Definition get_pl : CVM Plc :=
  st <- get ;;
  ret (st_pl st).

Definition modify_evm (f:EvidenceC -> EvidenceC) : CVM unit :=
  st <- get ;;
  let '{| st_ev := e; st_trace := tr; st_pl := p; st_store := store |} := st in
  put (mk_st (f e) tr p store).

Definition add_trace (tr':list Ev) : cvm_st -> cvm_st :=
  fun '{| st_ev := e; st_trace := tr; st_pl := p; st_store := store |} =>
    mk_st e (tr ++ tr') p store.

Definition add_tracem (tr:list Ev) : CVM unit :=
  modify (add_trace tr).

Definition split_ev_seq (i:nat) (sp1 sp2:SP) (e:EvidenceC) (p:Plc) : CVM (EvidenceC*EvidenceC) :=
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    add_tracem [Term_Defs.split i p] ;;
               ret (e1,e2).

Definition split_ev_par (i:nat) (sp1 sp2:SP) ((*loc_e1*) loc_e2:Loc)
           (*(t1 t2:AnnoTerm)*) (e:EvidenceC) (p:Plc) : CVM EvidenceC :=
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    (*let loc_e1 := fst (range t1) in
    let loc_e2 := fst (range t2) in *)
    (*put_store_at loc_e1 e1 ;; *)
    put_store_at loc_e2 e2 ;;
    add_tracem [splitp i (*loc_e1*) loc_e2 p] ;;
    ret e1.


(** * Partially-symbolic implementations of IO operations *)

Definition invokeUSM (x:nat) (i:ASP_ID) (l:list Arg) (e:EvidenceC) : CVM BS :=
  (*e <- get_ev ;; *)
  p <- get_pl ;;
  add_tracem [umeas x p i l];;
  ret x 
  (*ret (uuc i x e)*).

Definition encodeEv (e:EvidenceC) : BS.
Admitted.

Definition signEv (x:nat) (e:EvidenceC) : CVM BS :=
  (* e <- get_ev ;; *)
  p <- get_pl ;;
  add_tracem [sign x p] ;;
  ret x
  (*ret (ggc x e)*).


Definition hashEv (x:nat) (e:EvidenceC) : CVM BS :=
  (* e <- get_ev ;; *)
  p <- get_pl ;;
  add_tracem [hash x p] ;;
  ret x.

Definition copyEv (x:nat) : CVM EvidenceC :=
  p <- get_pl ;;
  add_tracem [copy x p] ;;
  get_ev.

Definition do_prim (x:nat) (a:ASP) : CVM EvidenceC :=
  match a with
  | CPY => copyEv x
  | ASPC asp_id args =>
    e <- get_ev ;;
    bs <- invokeUSM x asp_id args e ;;
    ret (uuc asp_id bs e)               
  | SIG =>
    e<- get_ev ;;
    bs <- signEv x e ;;
    ret (ggc bs e)
  | HSH =>
    e <- get_ev ;;
    bs <- hashEv x e ;;
    ret (hhc bs e)
  end.

Definition sendReq (t:AnnoTerm) (q:Plc) (reqi:nat) (req_loc:Loc) : CVM unit :=
  p <- get_pl ;;
  e <- get_ev ;;
  put_store_at req_loc e ;;
  add_tracem [req reqi req_loc p q (unanno t)].

Definition receiveResp (rpyi:nat) (rpy_loc:Loc) (q:Plc) : CVM EvidenceC :=
  e <- get_store_at rpy_loc ;;
  p <- get_pl ;;
  add_tracem [rpy (Nat.pred rpyi) rpy_loc p q] ;;
  ret e.

(* Primitive CVM Monad operations that require IO Axioms *)
Definition doRemote (t:AnnoTerm) (q:Plc) (reqi:nat) (rpyi:nat) : CVM unit :=
  e <- get_store_at reqi ;;
  add_tracem (remote_events t q) ;;
  put_store_at rpyi (toRemote t q e).


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
*)


(*
Definition runParThreads (t1 t2:AnnoTerm) (p:Plc) (loc_e1 loc_e1' loc_e2 loc_e2':Loc) : CVM unit :=
  el1 <- runParThread t1 p loc_e1 loc_e1' ;;
  el2 <- runParThread t2 p loc_e2 loc_e2' ;;
  add_tracem (shuffled_events el1 el2).
*)

Definition join_seq (n:nat) (p:Plc) (e1:EvidenceC) (e2:EvidenceC) : CVM unit :=
  put_ev (ssc e1 e2) ;;
  add_tracem [join n p].

Definition join_par (n:nat) (p:Plc) (*(xi:Loc)*) (e1r:EvidenceC) (yi:Loc) (*(e1:EvidenceC) (e2:EvidenceC)*) : CVM unit :=
  (*e1r <- get_store_at xi ;; *)
  e2r <- get_store_at yi ;;
  put_ev (ppc e1r e2r) ;;
  add_tracem [joinp n (*xi*) yi yi p].
  

(** * Helper functions for Appraisal *)

Definition extractUev (e:EvidenceC) : CVM (BS * EvidenceC) :=
  match e with
  | uuc i bs e' => ret (bs,e')
  | _ => failm
  end.

Definition extractSig (e:EvidenceC) : CVM (BS * EvidenceC) :=
  match e with
  | ggc bs e' => ret (bs, e')
  | _ => failm
  end.

(*
Definition extractHsh (e:EvidenceC) : CVM (BS * EvidenceC) :=
  match e with
  | hhc bs e' => ret (bs, e')
  | _ => failm
  end. *)


Definition extractComp (e:EvidenceC) : CVM (EvidenceC * EvidenceC) :=
  match e with
  | ssc e1 e2 => ret (e1,e2)
  (*| ppc e1 e2 => ret (e1,e2) *)
  | _ => failm
  end.

Definition checkSig (x:nat) (i:ASP_ID) (e':EvidenceC) (sig:BS) : CVM BS :=
  invokeUSM x i ([encodeEv e'] ++ [sig] (* ++ args*) ) mtc.

Definition checkUSM (x:nat) (i:ASP_ID) (l:list Arg) (bs:BS) : CVM BS :=
  invokeUSM x i ([bs] ++ l) mtc.
   
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
  add_tracem,
  modify_evm,
  split_ev_seq,
  join_par,
  add_trace,
  failm,
  (* Uncommenting these evaluates too much, can't apply lemmas *)
  (*get_store_at,*)
  get,
  when,
  put,
  nop,
  modify,
  bind,
  ret in *;
  simpl in *.




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
