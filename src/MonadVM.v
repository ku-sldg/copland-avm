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

Definition Event_ID := nat.

Definition CVM := St cvm_st.

(* VM monad operations *)

Definition put_ev (e:EvC) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let p' := st_pl st in
     put (mk_st e tr' p').

Definition put_pl (p:Plc) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let e' := st_ev st in
     put (mk_st e' tr' p).

Definition get_ev : CVM EvC :=
  st <- get ;;
  ret (st_ev st).

Definition get_pl : CVM Plc :=
  st <- get ;;
  ret (st_pl st).

Definition modify_evm (f:EvC -> EvC) : CVM unit :=
  st <- get ;;
  let '{| st_ev := e; st_trace := tr; st_pl := p |} := st in
  put (mk_st (f e) tr p).

Definition add_trace (tr':list Ev) : cvm_st -> cvm_st :=
  fun '{| st_ev := e; st_trace := tr; st_pl := p |} =>
    mk_st e (tr ++ tr') p.

Definition add_tracem (tr:list Ev) : CVM unit :=
  modify (add_trace tr).

Definition split_ev (i:Event_ID) (sp:Split): CVM (EvC*EvC) :=
  e <- get_ev ;;
  p <- get_pl ;;
  let e1 := splitEv_l sp e in
  let e2 := splitEv_r sp e in
  add_tracem [Term_Defs.split i p] ;;
  ret (e1,e2).

(** * Partially-symbolic implementations of IO operations *)

(*
Definition nat_to_bs (x:nat): BS.
Admitted.
*)

Definition do_asp (params :ASP_PARAMS) (mpl:Plc) (x:Event_ID) : BS.
Admitted.
         
Definition tag_ASP (params :ASP_PARAMS) (mpl:Plc) (x:Event_ID) : CVM unit :=
  match params with
  | asp_paramsC i l tpl tid => add_tracem [umeas x mpl i l tpl tid]
  end.


(* Matches on evidence type param only for verification.  
   Will extract to the cons function over the first two params (new measurement bits + existing evidence) *)
Definition cons_uu (x:BS) (e:EvC) (params:ASP_PARAMS) (mpl:Plc) : EvC :=
  match e with
  | evc bits et => evc (x :: bits) (uu params mpl et)
  end.

Definition invoke_ASP (params:ASP_PARAMS) (x:Event_ID) : CVM EvC :=
  e <- get_ev ;;
  p <- get_pl ;;
  tag_ASP params p x ;;
  ret (cons_uu (do_asp params p x) e params p).

Definition encodeEvBits (e:EvC): BS.
Admitted.

Definition do_sig (bs:BS) (p:Plc) (sigTag:Event_ID) : BS.
Admitted.

Definition do_hash (bs:BS) (p:Plc) : BS.
Admitted.

Definition tag_SIG (x:Event_ID) (p:Plc) (e:EvC) : CVM unit :=
  add_tracem [sign x p (get_et e)].

Definition cons_sig (sig:BS) (e:EvC) (p:Plc): EvC :=
  match e with
  | evc bits et => evc (sig :: bits) (gg p et)
  end.

Definition signEv (x:Event_ID) : CVM EvC :=
  p <- get_pl ;;
  e <- get_ev ;;
  tag_SIG x p e ;;
  ret (cons_sig (do_sig (encodeEvBits e) p x) e p).

Definition tag_HSH (x:Event_ID) (p:Plc) (e:EvC): CVM unit :=
  add_tracem [hash x p (get_et e)].

Definition cons_hh (hsh:BS) (e:EvC) (p:Plc): EvC :=
  match e with
  | evc _ et => evc [hsh] (hh p et)
  end.

Definition hashEv (x:Event_ID) : CVM EvC :=
  p <- get_pl ;;
  e <- get_ev ;;
  tag_HSH x p e ;;
  ret (cons_hh (do_hash (encodeEvBits e) p) e p).

Definition copyEv (x:Event_ID) : CVM EvC :=
  p <- get_pl ;;
  add_tracem [copy x p] ;;
  get_ev.

Definition do_prim (x:Event_ID) (a:ASP) : CVM EvC :=
  match a with
  | CPY => copyEv x
  | ASPC params =>
    invoke_ASP params x       
  | SIG => signEv x
  | HSH => hashEv x
  end.

(* Primitive monadic communication primitives (some require IO Axioms) *)

Definition tag_REQ (t:AnnoTerm) (p:Plc) (q:Plc) (e:EvC) (reqi:Event_ID) : CVM unit :=
  add_tracem [req reqi p q (unanno t) (get_et e)].

Definition tag_RPY (p:Plc) (q:Plc) (e:EvC) (rpyi:Event_ID) : CVM unit :=
  add_tracem [rpy (Nat.pred rpyi) p q (get_et e)].

Definition remote_session (t:AnnoTerm) (p:Plc) (q:Plc) (e:EvC) (reqi:Event_ID) : CVM EvC :=
  tag_REQ t p q e reqi ;;
  let e' := (doRemote_session t q e) in
  add_tracem (cvm_events t q (get_et e)) ;;
  ret e'.

Definition doRemote (t:AnnoTerm) (q:Plc) (e:EvC) (reqi:Event_ID) (rpyi:Event_ID) : CVM EvC :=
  p <- get_pl ;;
  e' <- remote_session t p q e reqi ;;
  tag_RPY p q e' rpyi ;;
  ret e'.

Definition ss_cons (e1:EvC) (e2:EvC): EvC :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (ss et1 et2)
  end.

Definition pp_cons (e1:EvC) (e2:EvC): EvC :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (pp et1 et2)
  end.

Definition join_seq (n:Event_ID) (e1:EvC) (e2:EvC): CVM unit :=
  p <- get_pl ;;
  put_ev (ss_cons e1 e2) ;;
  add_tracem [join (Nat.pred n) p].

(* Primitive monadic parallel CVM thread primitives (some require IO Axioms) *)

Definition do_start_par_threadIO (loc:Loc) (t:AnnoTerm) (e:RawEv) : unit.
Admitted.

Definition do_start_par_thread (loc:Loc) (t:AnnoTerm) (e:RawEv) : CVM unit :=
  let _ := do_start_par_threadIO loc t e in
  ret tt.  (* Admitted. *)

Definition start_par_thread (loc:Loc) (t:AnnoTerm) (e:EvC) : CVM unit :=
  p <- get_pl ;;
  do_start_par_thread loc t (get_bits e) ;;
  add_tracem [cvm_thread_start loc p t (get_et e)].

Definition do_wait_par_thread (loc:Loc) (t:AnnoTerm) (p:Plc) (e:EvC) : CVM EvC :=
  ret (parallel_vm_thread loc t p e).

Definition wait_par_thread (loc:Loc) (t:AnnoTerm) (e:EvC) : CVM EvC :=
  p <- get_pl ;;
  e' <- do_wait_par_thread loc t p e ;;
  add_tracem [cvm_thread_end loc] ;;
  ret e'.

Definition join_par (n:Event_ID) (e1:EvC) (e2:EvC): CVM unit :=
  p <- get_pl ;;
  put_ev (pp_cons e1 e2) ;;
  add_tracem [join (Nat.pred n) p].
   
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
