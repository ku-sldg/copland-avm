(* Tactics used throughout the proofs *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** Tactics that provide useful automation. *)

Ltac inv H := inversion H; clear H; subst.

(** Expand let expressions in both the antecedent and the
    conclusion. *)

Ltac expand_let_pairs :=
  match goal with
  | |- context [let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  | [ H: context [let (_,_) := ?e in _] |- _ ] =>
    rewrite (surjective_pairing e) in H
  end.

(** Destruct disjuncts in the antecedent without naming them.  *)

Ltac destruct_disjunct :=
  match goal with
  | [ H: _ \/ _  |- _ ] => destruct H as [H|H]
  end.
