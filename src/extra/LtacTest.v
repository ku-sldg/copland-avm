Ltac my_tac tac := tac.

Lemma foo : (1 = 1 /\ 2 = 2).
Proof.
  split; [reflexivity | reflexivity]. (* Succeeds as expected *)
  Undo.
  my_tac (split; [reflexivity | reflexivity]).  (* Syntax Error? *)
Qed.


  
