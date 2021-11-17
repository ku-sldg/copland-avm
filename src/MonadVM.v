(*
Definition of the CVM Monad + monadic helper functions.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term ConcreteEvidence Axioms_Io Evidence_Bundlers AutoPrim.
Require Import StructTactics.

Require Import Coq.Program.Tactics Lia.

Require Import List.
Import ListNotations.

Require Export StVM GenStMonad IO_Stubs.

Definition CVM := St cvm_st.

(* VM monad operations *)

Definition put_ev (e:EvC) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let p' := st_pl st in
     let i := st_evid st in
     put (mk_st e tr' p' i).

Definition put_pl (p:Plc) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let e' := st_ev st in
     let i := st_evid st in
     put (mk_st e' tr' p i).

Definition get_ev : CVM EvC :=
  st <- get ;;
  ret (st_ev st).

Definition get_pl : CVM Plc :=
  st <- get ;;
  ret (st_pl st).

Definition inc_id : CVM Event_ID :=
  st <- get ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let p' := st_pl st in
    let i := st_evid st in
    put (mk_st e' tr' p' (i + 1)) ;;
    ret i.
  

Definition modify_evm (f:EvC -> EvC) : CVM unit :=
  st <- get ;;
  let '{| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} := st in
  put (mk_st (f e) tr p i).

Definition add_trace (tr':list Ev) : cvm_st -> cvm_st :=
  fun '{| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} =>
    mk_st e (tr ++ tr') p i.

Definition add_tracem (tr:list Ev) : CVM unit :=
  modify (add_trace tr).

Definition split_ev (sp:Split): CVM (EvC*EvC) :=
  e <- get_ev ;;
  p <- get_pl ;;
  i <- inc_id ;;
  let e1 := splitEv_l sp e in
  let e2 := splitEv_r sp e in
  add_tracem [Term_Defs.split i p] ;;
  ret (e1,e2).

(** * Partially-symbolic implementations of IO operations *)

(*
Definition do_asp (params :ASP_PARAMS) (mpl:Plc) (x:Event_ID) : BS.
Admitted.
*)
         
Definition tag_ASP (params :ASP_PARAMS) (mpl:Plc) : CVM BS :=
  match params with
  | asp_paramsC i l tpl tid =>
    x <- inc_id ;;
    let bs := (do_asp params mpl x) in
    add_tracem [umeas x mpl i l tpl tid] ;;
    ret bs
  end.

Definition invoke_ASP (params:ASP_PARAMS) : CVM EvC :=
  e <- get_ev ;;
  p <- get_pl ;;
  bs <- tag_ASP params p ;;
  ret (cons_uu bs e params p).

Definition tag_SIG (p:Plc) (e:EvC) : CVM BS :=
  x <- inc_id ;;
  let bs := (do_sig (encodeEvBits e) p x) in
  add_tracem [sign x p (get_et e)];;
  ret bs.

Definition signEv : CVM EvC :=
  p <- get_pl ;;
  e <- get_ev ;;

  bs <- tag_SIG p e ;;
  ret (cons_sig bs e p).

Definition tag_HSH (p:Plc) (e:EvC): CVM BS :=
  x <- inc_id ;;
  let bs := (do_hash (encodeEvBits e) p) in
  add_tracem [hash x p (get_et e)] ;;
  ret bs.

Definition hashEv : CVM EvC :=
  p <- get_pl ;;
  e <- get_ev ;;
  bs <- tag_HSH p e ;;
  ret (cons_hh bs e p).

Definition copyEv : CVM EvC :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_tracem [copy x p] ;;
  get_ev.

Definition do_prim (a:ASP) : CVM EvC :=
  match a with
  | CPY => copyEv
  | ASPC params =>
    invoke_ASP params     
  | SIG => signEv
  | HSH => hashEv
  end.

Fixpoint event_id_span (t: Term) : nat :=
  match t with
  | asp x => 1

  | att p x => 2 + (event_id_span x)

  | lseq x y => (event_id_span x) + (event_id_span y)

  | bseq s x y => 2 + (event_id_span x) + (event_id_span y)

  | bpar s x y => 2 + (event_id_span x) + (event_id_span y)
  end.

Lemma span_range : forall t i j t',
  anno t i = (j, t') ->
  event_id_span t = (j - i).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
    try 
    cbn in *;
    find_inversion;
    lia.
  -
    cbn in *.
    repeat break_let.
    find_inversion.
    assert (event_id_span t = n - (S i)).
    { eauto. }
    rewrite H.
    assert (n > (S i)).
    {
      eapply anno_mono.
      eassumption.
    }
    lia.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span t1 = (n - i)) by eauto.
    assert (event_id_span t2 = (j - n)) by eauto.
    repeat jkjke.
    assert (n > i).
    { eapply anno_mono; eauto. }
    assert (j > n).
    { eapply anno_mono; eauto. }
    lia.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span t1 = (n - (S i))) by eauto.
    assert (event_id_span t2 = (n0 - n)) by eauto.
    repeat jkjke.
    assert (n > (S i)).
    { eapply anno_mono; eauto. }
    assert (n0 > n).
    { eapply anno_mono; eauto. }
    lia.
  -
        cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span t1 = (n - (S i))) by eauto.
    assert (event_id_span t2 = (n0 - n)) by eauto.
    repeat jkjke.
    assert (n > (S i)).
    { eapply anno_mono; eauto. }
    assert (n0 > n).
    { eapply anno_mono; eauto. }
    lia.
Defined.

Definition inc_remote_event_ids (t:Term) : CVM unit :=
  st <- get ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let p' := st_pl st in
    let i := st_evid st in
    let new_i := i + (event_id_span t) in
    put (mk_st e' tr' p' new_i).
  
(* Primitive monadic communication primitives (some require IO Axioms) *)

Definition tag_REQ (t:Term) (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  reqi <- inc_id ;;
  add_tracem [req reqi p q t (get_et e)].

Definition tag_RPY (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  rpyi <- inc_id ;;
  add_tracem [rpy rpyi p q (get_et e)].

Definition remote_session (t:Term) (p:Plc) (q:Plc) (e:EvC) : CVM EvC :=
  tag_REQ t p q e ;;
  let e' := (doRemote_session t q e) in
  add_tracem (cvm_events t q (get_et e)) ;;
  inc_remote_event_ids t ;;
  ret e'.

Definition doRemote (t:Term) (q:Plc) (e:EvC) : CVM EvC :=
  p <- get_pl ;;
  e' <- remote_session t p q e ;;
  tag_RPY p q e' ;;
  ret e'.

Definition join_seq (e1:EvC) (e2:EvC): CVM unit :=
  p <- get_pl ;;
  n <- inc_id ;;
  put_ev (ss_cons e1 e2) ;;
  add_tracem [join n p].

(* Primitive monadic parallel CVM thread primitives (some require IO Axioms) *)

(*
Definition do_start_par_threadIO (loc:Loc) (t:Term) (e:RawEv) : unit.
Admitted.
*)

Definition do_start_par_thread (loc:Loc) (t:Term) (e:RawEv) : CVM unit :=
  let _ := do_start_par_threadIO loc t e in
  ret tt.  (* Admitted. *)

Definition start_par_thread (loc:Loc) (t:Term) (e:EvC) : CVM unit :=
  p <- get_pl ;;
  do_start_par_thread loc t (get_bits e) ;;
  add_tracem [cvm_thread_start loc p t (get_et e)].

Definition do_wait_par_thread (loc:Loc) (t:Term) (p:Plc) (e:EvC) : CVM EvC :=
  ret (parallel_vm_thread loc t p e).

Definition wait_par_thread (loc:Loc) (t:Term) (e:EvC) : CVM EvC :=
  p <- get_pl ;;
  e' <- do_wait_par_thread loc t p e ;;
  add_tracem [cvm_thread_end loc] ;;
  inc_remote_event_ids t ;;
  ret e'.

Definition join_par (e1:EvC) (e2:EvC): CVM unit :=
  p <- get_pl ;;
  n <- inc_id ;;
  put_ev (pp_cons e1 e2) ;;
  add_tracem [join n p].
   
Ltac monad_unfold :=
  repeat unfold
  execSt,  
  do_prim,
  invoke_ASP,
  signEv,
  hashEv,
  copyEv,

  tag_HSH,
  doRemote,

  get_ev,
  get_pl,
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
                                                          
    | [H: {| st_ev := _; st_trace := _; st_pl := _(*; st_store := _*); st_evid := _ |} =
          {| st_ev := _; st_trace := _; st_pl := _ (*; st_store := _*); st_evid := _ |} |- _ ] =>
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
