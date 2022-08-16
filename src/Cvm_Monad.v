(*
Definition of the CVM Monad + monadic helper functions.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term ConcreteEvidence Axioms_Io Evidence_Bundlers Defs.
Require Import StructTactics.

Require Import Coq.Program.Tactics Lia.

Require Import List.
Import ListNotations.

Require Export Cvm_St StMonad_Coq IO_Stubs.

(* Helper that simulates encoding the raw bits portion of an evidence bundle.
   Note: encodeEvRaw is (as of now) an Admitted (abstract) operation.  *)
Definition encodeEvBits (e:EvC): BS :=
  match e with
  | (evc bits _) => encodeEvRaw bits
  end.

(** * CVM monadic primitive operations *)

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
    put (mk_st e' tr' p' (Nat.add i (S O))) ;;
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

(* TODO: consider removing split/join events from reference semantics.
         Would make this (no-op) helper unecessary. *)
Definition split_ev : CVM unit :=
  p <- get_pl ;;
  i <- inc_id ;;
  add_tracem [Term_Defs.split i p].


(** * Partially-symbolic implementations of IO operations *)

(* Generates a new event ID and adds a measurement event with that ID to the 
   CVM internal trace.  Returns the new Event_ID (used to represent raw 
   evidence, relevant for appraisal verification).  *)
Definition tag_ASP (params :ASP_PARAMS) (mpl:Plc) (e:EvC) : CVM Event_ID :=
  x <- inc_id ;;
  add_tracem [umeas x mpl params (get_et e)] ;;
  ret x.

(* Helper function that builds a new internal evidence bundle based on 
   the evidence extension parameter of an ASP term. *)
Definition fwd_asp (fwd:FWD) (bs:BS) (e:EvC) (p:Plc) (ps:ASP_PARAMS): EvC :=
  match fwd with
  | COMP => cons_hsh bs e p ps
  | EXTD => cons_gg bs e p ps
  | ENCR => cons_enc bs e p ps
  | KILL => cons_kill bs e p ps
  end.

(* Simulates invoking an arbitrary ASP.  Tags the event, builds and returns 
   the new evidence bundle. *)
Definition invoke_ASP (fwd:FWD) (params:ASP_PARAMS) : CVM EvC :=
  e <- get_ev ;;
  p <- get_pl ;;
  x <- tag_ASP params p e ;;
  bs <- do_asp' params (get_bits e) p x ;;
  ret (fwd_asp fwd bs e p params).

Definition copyEv : CVM EvC :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_tracem [copy x p] ;;
  get_ev.

Definition nullEv : CVM EvC :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_tracem [null x p] ;;
  ret mt_evc.

Definition clearEv : unit -> CVM EvC :=
  fun _ => ret mt_evc.

(* Helper that interprets primitive core terms in the CVM.  *)
Definition do_prim (a:ASP_Core) : CVM EvC :=
  match a with
  | NULLC => nullEv
  | CLEAR => clearEv tt
  | CPYC => copyEv
  | ASPCC fwd params => invoke_ASP fwd params
  end.

(* Computes the length of the "span" or range of event IDs for a given Term *)
(* TODO: consider changing this to event_id_span_Term *)
Fixpoint event_id_span' (t: Term) : nat :=
  match t with
  | asp x => 1
  | att p x => Nat.add (S (S O)) (event_id_span' x)
  | lseq x y => Nat.add (event_id_span' x) (event_id_span' y)
  | bseq s x y => Nat.add (S (S O)) (Nat.add (event_id_span' x) (event_id_span' y))
  | bpar s x y => Nat.add (S (S O)) (Nat.add (event_id_span' x) (event_id_span' y))
  end.

(* Same as event_id_span', but for Core Terms *)
(* TODO: consider changing this to event_id_span_Core *)
Fixpoint event_id_span (t: Core_Term) : nat :=
  match t with
  | aspc CLEAR =>  O
  | attc _ x => Nat.add (S (S O)) (event_id_span' x)
  | lseqc x y => Nat.add (event_id_span x) (event_id_span y)
  | bseqc x y => Nat.add (S (S O)) (Nat.add (event_id_span x) (event_id_span y))
  | bparc _ x y => Nat.add (S (S O)) (Nat.add (event_id_span x) (event_id_span y))
  | _ => S O
  end.

Lemma event_id_works : forall t,
  event_id_span' t = event_id_span (copland_compile t).
Proof with (simpl in *; eauto).
  induction t...
  - destruct a... destruct s...
  - destruct s, s, s0...
  - destruct s, s, s0...
Qed.


Lemma span_range : forall t i j t',
  anno t i = (j, t') ->
  event_id_span' t = (j - i).
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
    assert (event_id_span' t = n - (S i)).
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
    assert (event_id_span' t1 = (n - i)) by eauto.
    assert (event_id_span' t2 = (j - n)) by eauto.
    repeat jkjke.
    assert (n > i /\ j > n). {
      split; eapply anno_mono; eauto.
    }
    lia.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span' t1 = (n - (S i))) by eauto.
    assert (event_id_span' t2 = (n0 - n)) by eauto.
    repeat jkjke.
    assert (n > S i /\ n0 > n). {
      split; eapply anno_mono; eauto.
    }
    lia.
  -
        cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span' t1 = (n - (S i))) by eauto.
    assert (event_id_span' t2 = (n0 - n)) by eauto.
    repeat jkjke.
    assert (n > S i /\ n0 > n). {
      split; eapply anno_mono; eauto.
    }
    lia.
Defined.

(* Monadic helper function to simulate a span of remote event IDs 
   corresponding to the size of a Term *)
Definition inc_remote_event_ids (t:Term) : CVM unit :=
  st <- get ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let p' := st_pl st in
    let i := st_evid st in
    let new_i := Nat.add i (event_id_span' t) in
    put (mk_st e' tr' p' new_i).

(* Monadic helper function to simulate a span of parallel event IDs 
   corresponding to the size of a Core_Term *)
Definition inc_par_event_ids (t:Core_Term) : CVM unit :=
  st <- get ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let p' := st_pl st in
    let i := st_evid st in
    let new_i := Nat.add i (event_id_span t) in
    put (mk_st e' tr' p' new_i).
  
(* Primitive monadic communication primitives 
   (some rely on Admitted IO Stubs). *)

Definition tag_REQ (t:Term) (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  reqi <- inc_id ;;
  add_tracem [req reqi p q t (get_et e)].

Definition tag_RPY (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  rpyi <- inc_id ;;
  add_tracem [rpy rpyi p q (get_et e)].

Definition remote_session (t:Term) (p:Plc) (q:Plc) (e:EvC) : CVM EvC :=
  tag_REQ t p q e ;;
  e' <- doRemote_session' t q e ;;
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

(* Primitive monadic parallel CVM thread primitives 
   (some rely on Admitted IO Stubs). *)

Definition start_par_thread (loc:Loc) (t:Core_Term) (e:EvC) : CVM unit :=
  p <- get_pl ;;
  do_start_par_thread loc t (get_bits e) ;;
  add_tracem [cvm_thread_start loc p t (get_et e)].

Definition wait_par_thread (loc:Loc) (t:Core_Term) (e:EvC) : CVM EvC :=
  p <- get_pl ;;
  e' <- do_wait_par_thread loc t p e ;;
  add_tracem [cvm_thread_end loc] ;;
  inc_par_event_ids t ;;
  ret e'.
   
Ltac monad_unfold :=
  repeat unfold
  execSt,  
  do_prim,
  invoke_ASP,
  clearEv,
  copyEv,
  
  doRemote,

  get_ev,
  get_pl,
  add_tracem,
  modify_evm,
  add_trace,
  failm,
  get,
  when,
  put,
  nop,
  modify,
  bind,
  ret in * ;
  simpl in * .

(* Look for cvm_st hyps and destruct them *)
Ltac vmsts :=
  simpl in *;
  repeat
    match goal with
    | [H: cvm_st |- _] => destruct H
    end.

(* Same as vmsts, but without preceding simplification (simpl). *)
Ltac amsts :=
  repeat match goal with
         | H:cvm_st |- _ => destruct H
         end.

(* Grouping together some common hypothesis normalizations.  Inverting pairs of
   Some values, cvm_st equivalences, etc. *)
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
