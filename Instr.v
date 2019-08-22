Require Import Term.

Require Import List.
Import ListNotations.

(** * VM Instructions *)

Inductive Instr: Set :=
| copy: Instr
| kmeas: ASP_ID -> Plc -> (list Arg) -> Instr
| umeas: ASP_ID -> (list Arg) -> Instr
| sign: Instr
| hash: Instr
| reqrpy: Plc -> Plc -> Term -> Instr
| split: SP -> SP -> Instr
| besl: Instr -> Instr
| besr: Instr -> Instr
| bep: (list Instr) -> (list Instr) -> Instr
| joins: Instr
| joinp: Instr.

Definition eq_ev_dec:
  forall x y: Instr, {x = y} + {x <> y}.
Proof.
  intros.
  generalize dependent y.
  induction x;
    intros; destruct y; try (left; reflexivity); try (right; congruence).
  SearchAbout "eq_dec".
  destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  destruct (PeanoNat.Nat.eq_dec n n0);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_term_dec t t0); try (left; congruence); try (right; congruence).
    destruct (eq_sp_dec s s1);
    destruct (eq_sp_dec s0 s2);
    try (left; congruence); try (right; congruence).
    destruct (IHx y); try (left; congruence); try (right; congruence).
    destruct (IHx y); try (left; congruence); try (right; congruence).
    admit.
Admitted.
Hint Resolve eq_ev_dec.

Definition eq_li_dec:
  forall x y: (list Instr), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.
Hint Resolve eq_li_dec.

Definition asp_instr (t:ASP) (p:Plc) : Instr :=
  match t with
  | CPY => copy
  | KIM i p args => kmeas i p args
  | USM i args => umeas i args
  | SIG => sign
  | HSH => hash
  end.
Check map.
Fixpoint instr_compiler (t:Term) (p:Plc) : (list Instr) :=
  match t with
  | asp a => [asp_instr a p]
  | att q t' => [reqrpy p q t']
  | lseq t1 t2 =>
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    tr1 ++ tr2
  | bseq (sp1,sp2) t1 t2 =>
    let splEv := [split sp1 sp2] in
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    let evalL := map besl tr1 in
    let evalR := map besr tr2 in
    splEv ++ evalL ++ evalR ++ [joins]
  | bpar (sp1,sp2) t1 t2 =>
    let splEv := [split sp1 sp2] in
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    let tr := [bep tr1 tr2] in
    splEv ++ tr ++ [joinp]
  end.