Require Import List.
Import ListNotations.

Require Import Lia.

Require Import StructTact.StructTactics.

Lemma seq_nonzero_fact: forall n n',
    n > 0 -> 
    In 0 (seq n n') ->
    False.
Proof.
Admitted.

Lemma seq_fact' : forall n n',
    In n (seq 1 n') ->
    In (S n) (seq 2 n').
Proof.
  intros.
    generalizeEverythingElse n.
    induction n; destruct n'; intros;
      try solve_by_inversion.
    -
      simpl in *.
      destruct H;
        try solve_by_inversion.

      exfalso.
      eapply seq_nonzero_fact with (n:=2) (n':=n').
      lia.
      eassumption.
    -
      simpl in *.
      destruct H;
        try solve_by_inversion.

      destruct n.
      +
        left.
        tauto.
      +
        right.

        assert (2 <= (S (S n)) < 2 + n').
        {
          eapply in_seq.
          eassumption.
        }
Admitted.

Lemma seq_fact: forall n n',
    S n < S n' ->
    In (S n) (seq 1 n').
Proof.
  intros.
  generalizeEverythingElse n'.
  induction n'; destruct n; intros;
    try lia;
    try (simpl; eauto; tauto).
  -
    simpl.
    right.
    pose (IHn' n).

    assert (S n < S n') by lia.
    pose (i H0).

    eapply seq_fact'; eauto.
Defined.
