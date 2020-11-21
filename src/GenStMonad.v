(*
General definition of a state monad with error + monadic notations.

Author:  Adam Petz, ampetz@ku.edu
*)

(* Generalized State Monad *)
Definition St(S A : Type) : Type := S -> (option A) * S % type.

Definition ret {S A : Type} (a : A) : St S A := fun s => (Some a, s).

Definition bind {S A B : Type} (m : St S A) (f : A -> St S B) : St S B :=
  fun s =>
    let '(a, s') := m s in
    match a with
    | Some v =>
      let '(b, s'') := f v s' in
      (b, s'')
    | _ => (None,s')
    end.

Definition failm {S A : Type} : St S A := fun s => (None, s).
      

(* alias for ret *)
(*Definition write_output {S O} (o : O) : GenHandler1 S O := ret o.*)

Definition modify {S} (f : S -> S) : St S unit := fun s => (Some tt, f s).

Definition put {S} (s : S) : St S unit := fun _ => (Some tt, s).

Definition get {S} : St S S := fun s => (Some s, s).

Definition runSt {S A} (h : St S A) (s : S)  : (option A) * S % type :=
  h s.

Definition evalSt {S A} (h : St S A) (s : S) : option A :=
 fst (runSt h s).

Definition execSt {S A} (h : St S A) (s : S) : S :=
  snd ((*runSt*) h s).




Definition nop {S : Type} := @ret S _ tt.

Notation "a >> b" := (bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Definition gets {S} {A} (f:S -> A) : St S A :=
  st <- get ;;
  ret (f st).

Definition when {S A} (b : bool) (m : St S A) : St S unit :=
  if b then m ;; ret tt else nop.
