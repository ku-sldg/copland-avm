(*
    This files primary purpose is for running QuickCheck on the Copland Parser

    It is in its own file due to QuickCheck requiring a separate opam install
*)
From QuickChick Require Import QuickChick.
Require Import Term_Defs.
Require Import CopParser.
Require Import Maps.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
Import QcNotation. 
Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope string_scope.

(* Have to ignore some warning related to 
semBindOptSizeMonotonicIncl_r semBindOptSizeMonotonicIncl_l *)
Set Warnings "-extraction-logical-axiom".
Set Warnings "-extraction".

Set Typeclasses Debug.

(* Creating Generators *)


Derive Arbitrary for ascii.
#[local]
Instance showAscii : Show (ascii) :=
{
  show a := (String a EmptyString) 
}.
Derive Arbitrary for string.
Derive Arbitrary for nat.

(******************************************************************)
(* Extra General Purpose Generators *)
(******************************************************************)

(** Lowercase ascii *)
Definition ascii_from_range (min max : nat) : G ascii := 
  bind (choose (min,max)) (fun val =>
    ret (ascii_of_nat val)).

Definition correct_ascii_from_range (min max : nat) : ascii -> bool :=
  fun x => let x' : nat := nat_of_ascii x in
  andb (Nat.leb min x') (Nat.leb x' max).

Definition genLower : G ascii := ascii_from_range 97 122.
Definition isLowerCorrect : ascii -> bool := correct_ascii_from_range 97 122.
QuickChick (forAll (genLower) isLowerCorrect).

(** Digits *)
Definition genDigits : G ascii := ascii_from_range 48 57.
Definition isDigitsCorrect : ascii -> bool := correct_ascii_from_range 48 57.
QuickChick (forAll (genDigits) isDigitsCorrect).

(** Underscores *)
Definition genUnderScore : G ascii := ascii_from_range 95 95.
Definition isUnderScoreCorrect : ascii -> bool := correct_ascii_from_range 95 95.
QuickChick (forAll (genUnderScore) isUnderScoreCorrect).

(** Uppercase *)
Definition genUpper : G ascii := ascii_from_range 65 90.
Definition isUpperCorrect : ascii -> bool := correct_ascii_from_range 65 90.
QuickChick (forAll (genUpper) isUpperCorrect).

(** ID chars *)
Definition genIdChar : G ascii := 
  oneOf [genLower; genUpper; genDigits; genUnderScore].
Definition genIdCharCorrect (x : ascii) : bool :=
  orb ((correct_ascii_from_range 97 122) x)
    (orb ((correct_ascii_from_range 48 57) x) 
      (orb ((correct_ascii_from_range 95 95) x) ((correct_ascii_from_range 65 90) x)
      )
    ).

QuickChick (forAll (genIdChar) genIdCharCorrect).

(** Symbols *)
Fixpoint genSymbolTail (sz : nat) : G string :=
  match sz with
  | 0 => ret ""
  | S sz' => freq [
    (1, liftM (fun x => String x EmptyString) genIdChar) ;
    (sz, bind (genIdChar) (fun h => 
          bind (genSymbolTail sz') (fun t =>
            ret (String h t))))
    ]
  end.
Definition genSymbol : G string :=
  h <- genLower ;;
  tailSize <- choose (0,20) ;;
  t <- genSymbolTail tailSize ;;
  ret (String h t).

Definition genSymbolCorrect (s : string) : bool :=
  match CopParser.parseSymbol (CopParser.tokenize s) map_empty with
  | CopParser.SomeE (m, s, t) => (Nat.leb (List.length t) 0)
  | CopParser.NoneE _ => false
  end.

Fixpoint shrinkSymbolTail (s : string) : list (string) :=
  match s with
  | EmptyString => [""]
  | String h t => [t] ++ (map (fun t' => (String h t')) (shrinkSymbolTail t))
  end.

(* Only difference is that here, we enforce keeping the first letter 
  (as it might be the only lower-case letter) *)
Definition shrinkSymbol (s : string) : list (string) :=
  match s with
  | EmptyString => []
  | String h t => (map (fun t' => (String h t')) (shrinkSymbolTail t))
  end.

QuickChick (forAll genSymbol genSymbolCorrect).

(******************************************************************)
(** Plc *)
(******************************************************************)

(*** Show *)
#[local]
Instance showPlc : Show (Plc) :=
    {
        show p := let x : nat := p in
                  show x
    }.

Definition string_to_nat (ns : string) : nat :=
    fold_left 
        (fun n d => 10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
        (CopParser.list_of_string ns)
        0.

Conjecture showPlcValid : forall (n : Plc), string_to_nat (show n) = n.

QuickChick showPlcValid.

(*** Dec *)
#[local]
Instance decPlc (p1 p2 : Plc) : Dec (p1 = p2).
dec_eq. Defined.

(*** Gen *)
#[local]
Instance arbitraryPlc : Arbitrary (Plc). Defined.

(******************************************************************)
(** ASP_ID *)
(******************************************************************)

(*** Gen, GenSize, Shrink - All inherited from string *)
#[local]
Instance showASP_ID : Show (ASP_ID).
constructor. tauto. Defined.

(*** Dec *)
#[local]
Instance decASP_ID (a1 a2 : ASP_ID) : Dec (a1 = a2). 
dec_eq.
(* constructor. unfold ssrbool.decidable. 
generalize dependent a2.
induction a1.
- induction a2.
  * left. reflexivity.
  * right. intro C. inversion C.
- intro. destruct a2.
  * right. intro C. inversion C.
  * destruct (Ascii.eqb a a0) eqn:E.
    ** rewrite Ascii.eqb_eq in E. subst. destruct (IHa1 a2) as [H1 | H2]; subst.
      *** left. reflexivity.
      *** right. intro C. inversion C. congruence.
    ** rewrite Ascii.eqb_neq in E. right. intro C. inversion C. congruence. *)
Defined.

(*** Gen *)
#[local]
Instance genASP_ID : Gen (ASP_ID) :=
{
  arbitrary := genSymbol
}.

(*** Shrink *)
#[local] 
Instance shrinkASP_ID : Shrink (ASP_ID) :=
{
  shrink := shrinkSymbol
}.

(*** Arbitrary *)
#[local]
Instance arbitraryASP_ID : Arbitrary (ASP_ID). Defined.

(******************************************************************)
(** TARG_ID *)
(******************************************************************)

(*** Gen, GenSize, Shrink - All inherited from string *)
#[local]
Instance showTARG_ID : Show (TARG_ID).
constructor. tauto. Defined.

(*** Dec *)
#[local]
Instance decTARG_ID (t1 t2 : TARG_ID) : Dec (t1 = t2).
dec_eq. Defined.

(*** Gen *)
#[local]
Instance genTARG_ID : Gen (TARG_ID) :=
{ arbitrary := genSymbol }.

(*** Shrink *)
#[local]
Instance shrinkTARG_ID : Shrink (TARG_ID) :=
{ shrink := shrinkSymbol }.

(*** Arbitrary *)
#[local]
Instance arbitraryTARG_ID : Arbitrary (TARG_ID). Defined.

(******************************************************************)
(** Arg *)
(******************************************************************)

(*** Dec *)
#[local]
Instance decArg (a1 a2 : Arg) : Dec (a1 = a2).
constructor. unfold ssrbool.decidable.
(* We have to admit the equality here because we have no idea what Arg actually is *)
Admitted.

(*** Gen (list Arg) *)
(* Forcing this to be nil every time *)
Definition gListArg : G (list Arg) := ret nil.
#[local]
Instance shrinkListArg : Shrink (list Arg) :=
{
  shrink := (fun x => nil)
}.
#[local]
Instance genListArg : Gen (list Arg) :=
{
  arbitrary := gListArg
}.

(******************************************************************)
(** ASP_PARAMS *)
(******************************************************************)

(*** Show *)
Open Scope monad_scope.

Definition showASP_PARAMS_Aux 
    (aspp : ASP_PARAMS) `{_ : Show ASP_ID} `{_ : Show TARG_ID} `{Show Plc} : string :=
    match aspp with
    | (asp_paramsC a arg p t) =>
        show a ++ " " ++ show p ++ " " ++ show t
    end.

#[local]
Instance showASP_PARAMS : Show (ASP_PARAMS) :=
    {
        show asp := showASP_PARAMS_Aux asp
    }.

Compute (show (asp_paramsC "kim" nil 2 "ker")).
(*** Dec *)
#[local]
Instance decASP_PARAMS (a1 a2 : ASP_PARAMS): Dec (a1 = a2).
constructor. unfold ssrbool.decidable.
destruct a1, a2.
destruct (a =? a0) eqn:Asp.
- (* asp_id are equal *) 
  destruct (Nat.eqb p p0) eqn:Plc.
  * (* plc are equal *)
    destruct (t =? t0) eqn:Targ.
    ** (* Targ are equal *)
      rewrite String.eqb_eq in *. subst.
      rewrite Nat.eqb_eq in Plc. subst.
      generalize dependent l0.
      induction l; intros.
      *** destruct l0 eqn:E.
        **** left. reflexivity.
        **** right. intro. inversion H.
      *** destruct l0 eqn:E.
        **** right. intro. inversion H.
        **** specialize IHl with l1. destruct IHl.
          ***** inversion e. 
                (* Use of a possibly dangerous decidablity admittance about args *)
                pose proof (decArg a a1). inversion H.
                inversion dec.
            ****** subst. left. reflexivity.
            ****** right. intro. inversion H2. contradiction.
          ***** right. intro. inversion H. subst. apply n. reflexivity.
    ** right. intro. inversion H; subst. 
      rewrite String.eqb_refl in Targ. discriminate.
  * right. intro. inversion H; subst.
    rewrite Nat.eqb_refl in Plc. discriminate. 
- (* asp_id are not equal *)
  right. intro. inversion H; subst.
  rewrite String.eqb_refl in Asp. discriminate.
Defined. 

(*** Gen *)
Derive Arbitrary for ASP_PARAMS.
Sample (@arbitrary ASP_PARAMS _).

(** ASP *)
(*** Show *)
Definition showASP_Aux (a : ASP) : string :=
    match a with
    | NULL => "{}"
    | CPY => "_"
    | ASPC params => show params
    | SIG => "!"
    | HSH => "#"
    end.
    
#[local]
Instance showASP : Show (ASP) :=
{
    show := showASP_Aux
}.

(*** Dec *)

#[local]
Instance decASP (a1 a2 : ASP): Dec (a1 = a2).
constructor. unfold ssrbool.decidable.
destruct a1, a2; try (left; reflexivity); try (right; intro C; inversion C; fail).
pose proof (decASP_PARAMS a a0).
inversion H. inversion dec.
- left. subst. reflexivity.
- right. intro C. inversion C. contradiction.
Defined.

Derive Arbitrary for ASP.

