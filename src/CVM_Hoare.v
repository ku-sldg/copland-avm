(* 
Modified from:  https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Hoare.v

Author:  Adam Petz
*)

Require Import StVM MonadVM GenStMonad StructTactics Term_Defs.
Require Import StMonad_Hoare.

Require Import List.
Import ListNotations.

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

Import MyUniverse.
Import MyFunctionalImp.
Local Open Scope cmd_scope.

Definition get_tc:
  {{top}}
  get
  {{fun st _ st' => st = st'}}.
Proof.
  mysimp.
Defined.

Definition put_tc: forall in_st,
  {{top}}
    put in_st
  {{fun _ _ st' => st' = in_st}}.
Proof.
  mysimp.
Defined.

Definition failm_tc{A:Type}:
  {{top}}
    (failm: CVM A)
  {{fun _ (v:A) _ => v = v}} -> False.
Proof.
  unfold precomp.
  unfold postcomp.
  unfold top.
  mysimp.
  apply H; eauto.
  exact ConcreteEvidence.mtc.
  exact nil.
  exact 0.
  exact nil.
Defined.

Definition put_ev_tc: forall e,
  {{top}}
    put_ev e
    {{fun st _ st' =>
        st_ev st' = e /\
        st_pl st = st_pl st'
        /\ st_trace st = st_trace st'
        /\ st_store st = st_store st'}}.
Proof.
  intros.
  mysimp.
Defined.

Definition get_ev_tc:
  {{top}}
    get_ev 
    {{fun st v st' =>
        st = st' /\ v = st_ev st}}.
Proof.
  intros.
  mysimp.
Defined.

Definition get_pl_tc:
  {{top}}
    get_pl
    {{fun st v st' =>
        st = st' /\ v = st_pl st}}.
Proof.
  intros.
  mysimp.
Defined.
        
Definition invokeusm_tc: forall x i l e,
  {{top}}
    (invokeUSM x i l e)
    {{fun st v st' =>
        st_ev st = st_ev st' /\
        st_pl st = st_pl st' /\
        st_trace st' = st_trace st ++ [umeas x (st_pl st) i l] /\
        st_store st = st_store st' /\
        v = x}}.
Proof.
  intros.
  monad_unfold.
  mysimp.
Defined.

Definition add_tracem_tc: forall tr,
  {{top}}
    add_tracem tr
    {{fun st _ st' =>
        st_ev st = st_ev st' /\
        st_pl st = st_pl st' /\
        st_trace st' = st_trace st ++ tr /\
        st_store st = st_store st'}}.
Proof.
  intros.
  monad_unfold.
  mysimp.
Defined.

Require Import ConcreteEvidence.

Definition ev_asp (x:nat) (a:ASP) (e:EvidenceC) :=
  match a with
  | CPY => e
  | ASPC asp_id _ => (uuc asp_id x e)
  | SIG => (ggc x e)
  | HSH => (hhc x e)
  end.

Definition tr_asp (x:nat) (p:Plc) (a:ASP) :=
  match a with
  | CPY => copy x p
  | ASPC asp_id args => (umeas x p asp_id args)
  | SIG => sign x p
  | HSH => hash x p
  end.

Definition do_prim_tc: forall x a,
  {{top}}
    do_prim x a
    {{fun st v st' =>
        st_ev st = st_ev st' /\
        st_pl st = st_pl st' /\
        st_trace st' = st_trace st ++ [(tr_asp x (st_pl st) a)] /\
        st_store st = st_store st' /\
        v = ev_asp x a (st_ev st)

    }}.
Proof.
  intros.
  destruct a;
  monad_unfold;
  mysimp.
Defined.


    




  
  


  


(*
Definition swap_tc x y :
  {{fun h => lookup h x <> None /\ lookup h y <> None}}
  swap x y
  {{fun h _ h' => lookup h' y = lookup h x /\ lookup h' x = lookup h y}}.
Proof.
 *)


