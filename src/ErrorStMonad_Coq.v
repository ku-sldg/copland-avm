(*
General definition of a state monad with error + monadic notations, 
  borrowed/tweaked from:  https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v

Primary Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs.

(* Generic result type.  Parameterized by the success type (A) 
    and the error type (E). *)
Inductive ResultT (A:Type) (E:Type) : Type := 
| errC : E -> ResultT A E
| resultC : A -> ResultT A E.

Arguments errC {A} {E} e.
Arguments resultC {A} {E} a.

(* Generalized Error + State Monad *)
Definition Err(S A E: Type) : Type := S -> (ResultT A E) * S % type.

Definition ret {S A E : Type} (a : A) : Err S A E := fun s => (resultC a, s).

Definition bind {S A B E : Type} (m : Err S A E) (f : A -> Err S B E) : Err S B E :=
  fun s =>
    let '(a, s') := m s in
    match a with
    | resultC v =>
      let '(b, s'') := f v s' in
      (b, s'')
    | errC e => (errC e,s')
    end.

Definition failm {S A E : Type} (e:E) : Err S A E := fun s => (errC e, s).
      

(* alias for ret *)
(*Definition write_output {S O} (o : O) : GenHandler1 S O := ret o.*)

Definition modify {S E} (f : S -> S) : Err S unit E := fun s => (resultC tt, f s).

Definition put {S E} (s : S) : Err S unit E := fun _ => (resultC tt, s).

Definition get {S E} : Err S S E := fun s => (resultC s, s).

Definition runErr {S A E} (h : Err S A E) (s : S)  : (ResultT A E) * S % type :=
  h s.

Definition evalErr {S A E} (h : Err S A E) (s : S) : ResultT A E :=
 fst (runErr h s).

Definition execErr {S A E} (h : Err S A E) (s : S) : S :=
  snd (h s).

Definition nop {S E: Type} := @ret S _ E tt.

Notation "a >> b" := (bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity).

Definition gets {S} {A} {E} (f:S -> A) : Err S A E :=
  st <- get ;;
  ret (f st).

Definition when {S A E} (b : bool) (m : Err S A E) : Err S unit E :=
  if b then m ;; ret tt else nop.
