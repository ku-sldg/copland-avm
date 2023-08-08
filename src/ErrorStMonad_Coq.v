(*
General definition of a state monad with error + monadic notations, borrowed/tweaked from:  https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs.

Print option.
Locate option.

Inductive ErrorT (A:Type) : Type := 
| errStrC : StringT -> ErrorT A
| errRetC : A -> ErrorT A.

Arguments errStrC {A} s.
Arguments errRetC {A} a.

(* Generalized State Monad *)
Definition Err(S A : Type) : Type := S -> (ErrorT A) * S % type.

Definition ret {S A : Type} (a : A) : Err S A := fun s => (errRetC a, s).

Definition bind {S A B : Type} (m : Err S A) (f : A -> Err S B) : Err S B :=
  fun s =>
    let '(a, s') := m s in
    match a with
    | errRetC v =>
      let '(b, s'') := f v s' in
      (b, s'')
    | errStrC str => (errStrC str,s')
    end.

Definition failm {S A : Type} (str:StringT) : Err S A := fun s => (errStrC str, s).
      

(* alias for ret *)
(*Definition write_output {S O} (o : O) : GenHandler1 S O := ret o.*)

Definition modify {S} (f : S -> S) : Err S unit := fun s => (errRetC tt, f s).

Definition put {S} (s : S) : Err S unit := fun _ => (errRetC tt, s).

Definition get {S} : Err S S := fun s => (errRetC s, s).

Definition runErr {S A} (h : Err S A) (s : S)  : (ErrorT A) * S % type :=
  h s.

Definition evalErr {S A} (h : Err S A) (s : S) : ErrorT A :=
 fst (runErr h s).

Definition execErr {S A} (h : Err S A) (s : S) : S :=
  snd (h s).




Definition nop {S : Type} := @ret S _ tt.

Notation "a >> b" := (bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity).

Definition gets {S} {A} (f:S -> A) : Err S A :=
  st <- get ;;
  ret (f st).

Definition when {S A} (b : bool) (m : Err S A) : Err S unit :=
  if b then m ;; ret tt else nop.
