(* 
Modified from:  https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Hoare.v

Author:  Adam Petz
*)

Require Import StVM MonadVM GenStMonad StructTactics Term_Defs.
Require Import StMonad_Hoare.

Require Import List.
Import ListNotations.

Require Import CVM_Hoare.
Require Import Impl_vm Term Auto.

(*
Module MyUniverse <: UNIVERSE.
 (** Alas, our universe of storable values cannot be big enough
     to store computations.  If we try to add computations to the
     types in U, we get a non-positive occurrence.  In short, you
     seem to need generally recursive types to build storable
     commands.  Not suprisingly, this leads to termination problems,
     as we can use Landin's knot to build a diverging computation... *)
(*
  Inductive U : Type := 
  | Nat_t : nat -> U
  | Pair_t : U -> U -> U.

  Definition t := U. *)
  Definition heap := cvm_st.
  Definition empty_heap := empty_vmst.
End MyUniverse.

Module MyFunctionalImp := MonadHoare(MyUniverse).
*)

Import MyUniverse.
Import MyFunctionalImp.

Local Open Scope cmd_scope.

Check get_tc.

Definition pl_immut_tc: forall t,
  {{fun _ => well_formed t}}
  copland_compile t
  {{fun st _ st' =>
      st_pl st = st_pl st'}}.
Proof.
  intros.
  induction t;
    try destruct a; (* asp case *)
    repeat (df; mysimp; dohtac); (* at case + others *)

    try ( (* lseq case *)
        do_wf_pieces;
        try specialize IHt1 with (h:=h);
        try specialize IHt2 with (h:=c0);
        repeat concludes;
        repeat subst';
        tauto).
Defined.

Definition compile_some_tc t:
  {{fun _ => well_formed t}}
  copland_compile t
  {{fun _ _ => top}}.
Proof.

  (*
  Check bind_tc.
  induction t;
    monad_unfold;
    repeat break_let.
  -
    destruct a;
      repeat mysimp.
  -
    intros.
    eapply consequence_tc.
    eapply bind_tc; intros.
    mysimp.

    
    admit.
    eapply consequence_tc.
    eapply bind_tc; intros.
    admit.
    eapply consequence_tc.
    eapply bind_tc; intros.
    admit.
    admit.
    intros.
    admit.
    intros.

    
    repeat (mysimp; monad_unfold).
    monad_unfold.
  eapply bind_tc.
  eapply bind_tc.
  monad_unfold.
  mysimp.
  mysimp.

  eapply consequence_tc.

  
  eapply bind_tc.

  
  monad_unfold.
  unfold copland_compile
  intros.

  eapply bind_tc.

*)
  
  induction t.
  -
    destruct a;
      df;
      mysimp.
    (*
  -
    repeat (df; mysimp; (*unfold get_store_at in *;*) dohtac ). *)
  -
    repeat (df; mysimp; (*unfold get_store_at in *;*) dohtac );
    do_wf_pieces.
    specialize IHt1 with (h:=h).
    repeat find_rewrite.
    eauto.

    specialize IHt1 with (h:=h).
    repeat find_rewrite. 

    specialize IHt2 with (h:=c0).
    repeat find_rewrite.
    eauto.

    specialize IHt1 with (h:=h).
    specialize IHt2 with (h:=c).
    find_rewrite.
    eauto.
Defined.

Require Import MonadVMFacts.
Require Import Helpers_VmSemantics.


Definition trace_irrel_store_tc: forall t tr1 tr1' (*tr2*) e e' p1' p1 o' o,
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    {{fun st =>
        st_ev st = e /\
        st_pl st = p1 /\
        st_store st = o

    }}
  copland_compile t
  {{fun st v st' =>
      st_store st' = o'


  }}.
Proof.
  intros.
  mysimp; try solve_by_inversion.
  -
  vmsts.
  (*
  destruct (copland_compile t {| st_ev := e; st_trace := ; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl. 
  do_asome. *)
  subst.
  destruct h.
  df.
  subst.
  df.
  dohi.
  df.
  tauto.
  -
    destruct h.
    df.
    Check always_some.
    assert (None = Some tt).
    eapply always_some.
    eassumption.
    eassumption.
    solve_by_inversion.
Defined.

Definition trace_irrel_pl_tc: forall t tr1 tr1' (*tr2*) e e' p1' p1 o' o,
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    {{fun st =>
        st_ev st = e /\
        st_pl st = p1 /\
        st_store st = o

    }}
  copland_compile t
  {{fun st v st' =>
      st_pl st' = p1'


  }}.
Proof.
  intros.
  mysimp; try solve_by_inversion.
  -
  vmsts.
  (*
  destruct (copland_compile t {| st_ev := e; st_trace := ; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl. 
  do_asome. *)
  subst.
  destruct h.
  df.
  subst.
  df.
  dohi.
  df.
  tauto.
  -
    destruct h.
    df.
    Check always_some.
    assert (None = Some tt).
    eapply always_some.
    eassumption.
    eassumption.
    solve_by_inversion.
Defined.

Definition trace_irrel_ev_tc: forall t tr1 tr1' (*tr2*) e e' p1' p1 o' o,
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    {{fun st =>
        st_ev st = e /\
        st_pl st = p1 /\
        st_store st = o

    }}
  copland_compile t
  {{fun st v st' =>
      st_ev st' = e'


  }}.
Proof.
  intros.
  mysimp; try solve_by_inversion.
  -
  vmsts.
  (*
  destruct (copland_compile t {| st_ev := e; st_trace := ; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl. 
  do_asome. *)
  subst.
  destruct h.
  df.
  subst.
  df.
  dohi.
  df.
  tauto.
  -
    destruct h.
    df.
    Check always_some.
    assert (None = Some tt).
    eapply always_some.
    eassumption.
    eassumption.
    solve_by_inversion.
Defined.

(*
Definition st_trace_irrel_tc: forall t tr1 tr1' (*tr2*) e e' p1' p1 o' o,
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    {{fun st =>
        st_ev st = e /\
        st_pl st = p1 /\
        st_store st = o

    }}
  copland_compile t
  {{fun st v st' =>
      st_ev st' = e' /\
      st_pl st' = p1' /\
      st_store st' = o'


  }}.
Proof.
  intros.
  repeat mysimp.
  df.
  vmsts.
  df.
  Check trace_irrel_ev.
  eapply trace_irrel_ev.
  
  eapply consequence_tc.
  eapply 
  admit.
  admit.
  mysimp.
  Focus 4.
*)
    
