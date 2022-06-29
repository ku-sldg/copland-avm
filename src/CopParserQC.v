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

(* Set Typeclasses Debug. *)


Ltac kill_false := let C := fresh "CONTRA" in
                   intro C; inversion C; congruence.

Ltac adec := try (left; reflexivity); try (right; kill_false).

Ltac qinv H := inversion H; subst; clear H.

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
  (* NOTE: We enforce a size limit here, it is questionable
           if we can really justify this as arbitrary then.
           But, I have faith that if it can work for any string length 1-21
           the parser will work for any string. the buck has to stop somewhere
           might as well be here *)
  t <- genSymbolTail tailSize ;;
  ret (String h t).

Definition genSymbolCorrect (s : string) : bool :=
  match CopParser.parseSymbol (CopParser.tokenize s) map_empty with
  | CopParser.SomeE (m, s, t) => (Nat.leb (List.length t) 0)
  | CopParser.NoneE _ => false
  | CopParser.OutOfFuel => false
  end.

Fixpoint shrinkSymbolTail (s : string) : list (string) :=
  match s with
  | EmptyString => []
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
(******************************************************************)
(******************************************************************)
(*               Starting Copland Generators                      *)
(******************************************************************)
(******************************************************************)
(******************************************************************)


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
Definition plc_equality (plc1 plc2 : Plc) : bool := Nat.eqb plc1 plc2.

#[local]
Instance decPlc (p1 p2 : Plc) : Dec (p1 = p2).
constructor. unfold ssrbool.decidable.
generalize dependent p2.
induction p1; destruct p2; adec.
specialize IHp1 with p2.
destruct IHp1; adec. left. auto.
Defined.

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
Definition asp_id_equality (a1 a2 : ASP_ID) : bool := String.eqb a1 a2.

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

(*** Show TARG_ID *)
#[local]
Instance showTARG_ID : Show (TARG_ID).
constructor. tauto. Defined.

(*** Dec *)
Definition targ_id_equality (t1 t2 : TARG_ID) : bool := String.eqb t1 t2.

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
dec_eq.
Defined.

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
(* Split *)
(******************************************************************)

(** We must first address SP *)
#[local]
Instance showSP : Show (SP) :=
{
  show x := match x with ALL => "+" | NONE => "-" end
}.

(** Dec SP*)
#[local]
Instance decSP (sp1 sp2 : SP) : Dec (sp1 = sp2).
dec_eq. Defined.

Derive Arbitrary for SP.
(* Sample (@arbitrary SP _). *)

(** Show Split *)
#[local]
Instance showSplit : Show (Split) :=
{
  show sp := let (s1,s2) := sp in show s1 ++ " " ++ show s2
}.

(** Dec Split *)
#[local]
Instance decSplit (sp1 sp2 : Split) : Dec (sp1 = sp2).
dec_eq. Defined.

(** G Split *)
Definition gSplit : G Split :=
  s1 <- (@arbitrary SP _) ;;
  s2 <- (@arbitrary SP _) ;;
  ret (s1, s2).

(** Gen Split *)
#[local]
Instance genSplit : Gen Split :=
{
  arbitrary := gSplit
}.

(** Shrink Split *)
Definition shrinkSplit_Aux (s : Split) : list (Split) :=
  match s with
  | (NONE, NONE) => []
  | (NONE, ALL) => [(NONE, NONE)]
  | (ALL, NONE) => [(NONE, NONE); (NONE, ALL)]
  | (ALL, ALL) => [(NONE, NONE); (NONE, ALL); (ALL, NONE)]
  end.

(** Arbitrary Split*)
#[local]
Instance arbitrarySplit : Arbitrary (Split). Defined.


(******************************************************************)
(** FWD *)
(******************************************************************)
(*** Show FWD *)
#[local]
Instance showFwd : Show (FWD) :=
{ show x := "" }.
(*** Dec FWD *)
#[local]
Instance decFwd (f1 f2 : FWD) : Dec (f1 = f2).
dec_eq. Defined.
(*** G FWD *)
Definition gFWD : G (FWD) := ret EXTD.
(*** Gen FWD *)
#[local]
Instance genFWD : Gen (FWD) :=
{ arbitrary := gFWD }.
(*** Shrink FWD *)
Definition shrinkFWD_Aux (f : FWD) : list (FWD) :=
  match f with
  | EXTD => []
  | COMP => [EXTD]
  end.
#[local]
Instance shrinkFWD : Shrink (FWD) :=
{ shrink := shrinkFWD_Aux }.
(*** Arbitrary FWD *)
#[local]
Instance arbitraryFWD : Arbitrary (FWD). Defined. 


(******************************************************************)
(** ASPC and ASP_PARAMS *)
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
dec_eq.
Defined.

(*** Gen *)
(* Safe to do here, because we already locked in the rest of the sub-terms arbitraries *)
Derive Arbitrary for ASP_PARAMS.


Definition genASP_PARAMS_Correct (a : ASP_PARAMS) : bool :=
  match CopParser.parseASPC (CopParser.tokenize (show a)) map_empty with
  | CopParser.SomeE (m, s, t) => (Nat.leb (List.length t) 0)
  | CopParser.NoneE _ => false
  | CopParser.OutOfFuel => false
  end.

QuickChick genASP_PARAMS_Correct.

(* Sample (@arbitrary ASP_PARAMS _). *)

(******************************************************************)
(** ASP *)
(******************************************************************)

(*** Show *)
Definition showASP_Aux (a : ASP) : string :=
    match a with
    | NULL => "{}"
    | CPY => "_"
    | ASPC sp fwd params => show params
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
inversion H. inversion dec; subst;
destruct s, s0, f, f0; adec.
Defined.

(*** G ASP *)
Definition gASP : G ASP :=
  oneOf [
    (ret NULL) ; (ret CPY) ; (ret SIG) ; (ret HSH) ;
    (par <- arbitrary ;; ret (ASPC ALL EXTD par))
  ].

(*** Gen ASP *)
#[local]
Instance genASP : Gen (ASP) :=
{ arbitrary := gASP }.

(*** Shrink ASP *)
Definition shrinkASP_Aux (a : ASP) : list (ASP) :=
  match a with
  | (ASPC sp fwd par) => map (fun p' => (ASPC sp fwd p')) (shrink par)
  | _ => [] (* If its just a basic ASP we cant shrink *)
  end.

#[local]
Instance shrinkASP : Shrink (ASP) :=
{
  shrink := shrinkASP_Aux
}.

(*** Arbitrary ASP *)
#[local]
Instance arbitraryASP : Arbitrary (ASP). Defined.

(* Sample (@arbitrary ASP _). *)

(*** Testing *)
Definition genASP_Correct (a : ASP) : bool :=
  match CopParser.parseASP (CopParser.tokenize (show a)) map_empty with
  | CopParser.SomeE (m, s, t) => (Nat.eqb (List.length t) 0)
  | CopParser.NoneE _ => false
  | CopParser.OutOfFuel => false
  end.

QuickChick genASP_Correct.

Definition genASP_parse_correct (a : ASP) : option ASP :=
  match CopParser.parseASP (CopParser.tokenize (show a)) map_empty with
  | CopParser.SomeE (_, (asp a'), _) => Some a'
  | _ => None
  end.

#[local]
Instance decEqOptionAsp : Dec_Eq (option ASP). dec_eq. Defined.

Conjecture genASP_works : forall (a : ASP), (genASP_parse_correct a) = Some a.
QuickChick genASP_works.

(******************************************************************)
(* Term *)
(******************************************************************)
(** Show Term *)
Fixpoint showTerm_Aux (t : Term) : string :=
  match t with
  | asp a => show a
  | att p t' => "@" ++ show p ++ " (" ++ showTerm_Aux t' ++ ")"
  | lseq t1 t2 => "((" ++ showTerm_Aux t1 ++ ") -> (" ++ showTerm_Aux t2 ++ "))"
  | bseq (s1,s2) t1 t2 => 
    "((" ++ showTerm_Aux t1 ++ ") " ++ show s1 ++ "<" ++ show s2 ++ " (" ++ showTerm_Aux t2 ++ "))"
  | bpar (s1,s2) t1 t2 =>
    "((" ++ showTerm_Aux t1 ++ ") " ++ show s1 ++ "~" ++ show s2 ++ " (" ++ showTerm_Aux t2 ++ "))"
  end.

#[local]
Instance showTerm : Show (Term) :=
{
  show := showTerm_Aux
}.


(** Dec Term *)
#[local]
Instance decTerm (t1 t2 : Term) : Dec (t1 = t2).
constructor. unfold ssrbool.decidable.
generalize dependent t2.
induction t1; intros; try (destruct a, a0); try (destruct t2);
adec.
- pose proof (decASP a a0).
  qinv H. qinv dec; adec.
- destruct (Nat.eqb p p0) eqn:plc.
  * (* places equal*)
    rewrite Nat.eqb_eq in *. subst. specialize IHt1 with t2.
    destruct IHt1; subst; adec.
  * rewrite Nat.eqb_neq in *. subst; adec.
- specialize IHt1_1 with t2_1. specialize IHt1_2 with t2_2.
  destruct IHt1_1; destruct IHt1_2; simpl; subst; adec.
- destruct s, s0, s, s1, s0, s2; adec;
  specialize IHt1_1 with t2_1; specialize IHt1_2 with t2_2;
  destruct IHt1_1; destruct IHt1_2; simpl; subst; adec.
- destruct s, s0, s, s1, s0, s2; adec;
  specialize IHt1_1 with t2_1; specialize IHt1_2 with t2_2;
  destruct IHt1_1; destruct IHt1_2; simpl; subst; adec.
Defined.

#[local]
Instance decEqTerm (t1 t2 : Term) : Dec_Eq (Term).
dec_eq. Defined.

(** G Term *)
Fixpoint gTerm (sz : nat) : G Term :=
  match sz with
  (* Base case, we just use a ASP as they are functionally terminals *)
  | 0 => term <- arbitrary ;; ret (asp term)
  | S f' => freq [
      (1, term <- arbitrary ;; ret (asp term)) ; 
      (Nat.mul 10 sz, p <- arbitrary ;; t' <- (gTerm f') ;; ret (att p t')) ;
      (Nat.mul 10 sz, t1 <- (gTerm f') ;; t2 <- (gTerm f') ;; ret (lseq t1 t2)) ;
      (Nat.mul 10 sz, sp <- arbitrary ;; t1 <- (gTerm f') ;; t2 <- (gTerm f') ;; ret (bseq sp t1 t2)) ;
      (Nat.mul 10 sz, sp <- arbitrary ;; t1 <- (gTerm f') ;; t2 <- (gTerm f') ;; ret (bpar sp t1 t2))
    ]
  end.

(* Sample (bind (choose (1,5)) (fun x => gTerm x)). *)

(** Gen Term *)
#[local]
Instance genTerm : Gen (Term) :=
{ arbitrary := sized (fun x => gTerm (S x)) }.

(** Shrink Term *)
Definition shrinkTerm_Aux (t : Term) : list (Term) :=
  match t with
  | asp a => (map (fun a' => asp a') (shrink a))
  (* | _ => []  *)
  (* Testing to see how detrimental the shrink is*)
  | att p t' => 
    (* vary p or vary t *)
    [t'] 
    (* ++ 
    (map (fun p' => att p' t) (shrink p)) ++ 
    (map (fun t'' => att p t'') (shrinkTerm_Aux t')) *)
  | lseq t1 t2 =>
    [t1 ; t2] 
    (* ++ 
    (map (fun t1' => lseq t1' t2) (shrinkTerm_Aux t1)) ++
    (map (fun t2' => lseq t1 t2') (shrinkTerm_Aux t2)) *)
  | bseq sp t1 t2 =>
    [t1 ; t2] ++ (* Vary sp, t1 or t2*)
    (map (fun sp' => bseq sp' t1 t2) (shrink sp)) 
    (* ++
    (map (fun t1' => bseq sp t1' t2) (shrinkTerm_Aux t1)) ++
    (map (fun t2' => bseq sp t1 t2') (shrinkTerm_Aux t2)) *)
  | bpar sp t1 t2 =>
    [t1 ; t2] ++ (* Vary sp, t1 or t2*)
    (map (fun sp' => bpar sp' t1 t2) (shrink sp)) 
    (* ++
    (map (fun t1' => bpar sp t1' t2) (shrinkTerm_Aux t1)) ++
    (map (fun t2' => bpar sp t1 t2') (shrinkTerm_Aux t2)) *)
  end.

#[local]
Instance shrinkTerm : Shrink (Term) :=
{ shrink := shrinkTerm_Aux }.

(** Arbitrary Term *)
#[local]
Instance arbitraryTerm : Arbitrary (Term). Defined.

(** Testing *)

Fixpoint term_seq_size (t : Term) : nat :=
  match t with
  | asp _ => 0
  | att _ t' => 1 + term_seq_size t'
  | lseq t1 t2 => 1 + term_seq_size t1 + term_seq_size t2
  | bseq sp t1 t2 => 1 + term_seq_size t1 + term_seq_size t2
  | bpar sp t1 t2 => 1 + term_seq_size t1 + term_seq_size t2
  end.

Definition term_fuel (t : Term) : nat := Nat.mul 10 (S (term_seq_size t)).

Definition genTerm_Correct (a : Term) : bool :=
  match CopParser.parsePhrase (term_fuel a) (CopParser.tokenize (show a)) map_empty with
  | CopParser.SomeE (m, s, t) => (Nat.leb (List.length t) 0)
  | CopParser.NoneE _ => false
  | CopParser.OutOfFuel => true
  end.

Definition stat_collect_prop (t : Term) :=
  (fun t => collect (term_seq_size t) true).
QuickChickWith (updMaxSize stdArgs 9) stat_collect_prop.

Open Scope cop_ent_scope.

Definition parse_succeeds' (a : Term) :=
  match CopParser.parsePhrase (term_fuel a) (CopParser.tokenize (show a)) map_empty with
  | CopParser.SomeE _ => (collect (term_seq_size a) true)
  | CopParser.NoneE _ => (collect (term_seq_size a) false)
  | CopParser.OutOfFuel => ((collect (term_seq_size a) false))
  end.


Definition parse_succeeds (a : Term) :=
  match CopParser.parsePhrase (term_fuel a) (CopParser.tokenize (show a)) map_empty with
  | CopParser.SomeE _ => (true)
  | CopParser.NoneE _ => (false)
  | CopParser.OutOfFuel => (false)
  end.

(* Extract Constant defNumTests   => "100000". *)
(* Extract Constant defSize        => "7". *)
Extract Constant defNumShrinks => "0".

(* QuickChick parse_succeeds'. *)

Conjecture all_terms_parseable : forall (a : Term), (parse_succeeds a) = true.
QuickChick all_terms_parseable.

Definition DEBUG_parse (s : string) : option Term :=
  match (CopParser.parsePhrase 100 (CopParser.tokenize s) map_empty) with
  | CopParser.SomeE (_, a', _) => Some a'
  | CopParser.NoneE _ => None
  | CopParser.OutOfFuel => None
  end.

Definition parse_to_out (a : Term) : option (Term) :=
  match (CopParser.parsePhrase (term_fuel a) (CopParser.tokenize (show a)) map_empty) with
  | CopParser.SomeE (_, a', _) => Some a'
  | CopParser.NoneE _ => None
  | CopParser.OutOfFuel => None
  end.

#[local]
Instance decEqOptionTerm : Dec_Eq (option Term).
dec_eq. Defined.

(* Extract Constant defNumTests => "100000". 
It passes this, but seems excessive for everytime we run
*)
Extract Constant defSize => "10".

Conjecture parsed_terms_match : forall (a : Term), (parse_to_out a) = Some a.
QuickChick parsed_terms_match.
