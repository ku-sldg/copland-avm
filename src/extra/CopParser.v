(*  Copland language definition.
    
   -Term(T):  Copland Phrase AST.
*)

From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Term_Defs.
Require Import Anno_Term_Defs.
Require Import Maps.
Require Import EqClass ID_Type.

Module CopParser.
Open Scope cop_ent_scope.
(* Using Tokenization Functionality from ImpParser.v - Logical Foundations - B. Pierce *)

(* ================================================================= *)
(** ** Lexical Analysis *)

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32)   (* space *)
           (n =? 9))   (* tab *)
      (orb (n =? 10)   (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Definition isAlphaNum (c : ascii) : bool :=
    orb (orb (isAlpha c) (isLowerAlpha c)) (isDigit c).

Definition isUnderscore (c : ascii) : bool :=
    (nat_of_ascii c) =? 95.

Inductive chartype := white | alpha | digit | underscore | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else if isUnderscore c then
    underscore
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    (* parse brackets and parens as their own tokens *)
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, _, "["      =>
      tk ++ ["["]::(tokenize_helper other [] xs')
    | _, _, "]"      =>
      tk ++ ["]"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | _,alpha,x  => (* if we see an alpha, proceed it like a match*)
      tokenize_helper alpha (x::acc) xs'
    | _, underscore, x => 
      tokenize_helper underscore (x::acc) xs'
    | _,digit,x  => 
    (* no individual digits should be around, if they are catch at parse not tokenizing *)
      tokenize_helper digit (x::acc) xs'
    | _,other,x  => 
    (* others must be treated normally, then dealt with at parse time *)
      tokenize_helper other (x::acc) xs'
    end
  end %char.

Lemma list_of_string_app : forall str1 str2,
  list_of_string (str1 ++ str2) = list_of_string str1 ++ list_of_string str2.
Proof.
  intros.
  induction str1.
  - simpl. reflexivity.
  - simpl. rewrite IHstr1. reflexivity.
Qed.

Lemma list_of_string_cons : forall a str1 a0 astr,
  list_of_string (String a str1) = a0 :: astr 
  <-> a = a0 /\ list_of_string str1 = astr.
Proof.
  split; intros.
  - inversion H. auto.
  - destruct H. auto. simpl. rewrite H0.  rewrite H. reflexivity.
Qed.

Lemma list_of_string_space :
  list_of_string " " = [" "%char].
Proof.
  auto.
Qed.
(* 
This proof takes too long, but works
Uncomment if ever needed

Lemma tokenize_helper_space_after : forall c st (t1 : string),
  tokenize_helper c st (list_of_string t1) 
  = tokenize_helper c st (list_of_string (t1 ++ " ")).
Proof.
  intros.
  generalize dependent c.
  generalize dependent st.
  induction t1.
  - simpl. destruct st eqn:E.
    * reflexivity.
    * rewrite app_nil_r. reflexivity.
  - destruct (list_of_string (String a t1)) eqn:AT.
    * inversion AT.
    * intros.
      rewrite list_of_string_app. rewrite AT.
      inversion AT.
      subst.
      destruct a0; destruct b,b0,b1,b2,b3,b4,b5,b6;
      simpl; intros; rewrite list_of_string_app in IHt1;
      rewrite <- list_of_string_space; 
      try (apply IHt1);
      try (rewrite IHt1; reflexivity).
Qed. *)

Ltac createBase char := 
  assert (Ht : char <> "["%char /\
     char <> "]"%char /\
     char <> "("%char /\ char <> ")"%char) by now 
      split; [ intros C; discriminate |
      split; [ intros C; discriminate | 
      split; intros C; discriminate ] ].

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize1 : 
    tokenize "hello world, this is a (simple) test! var bob; var b_b; var b1hello_bob icansay 123 heybob#" % string
    = 
    ["hello";"world,"; "this"; "is";"a";"(";"simple";")";"test!";"var";"bob;";"var";"b_b;";"var";"b1hello_bob";"icansay";"123";"heybob#"] % string .
unfold tokenize. reflexivity. Qed.

(* Error Message Options *)
Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string)
  | OutOfFuel.

Arguments SomeE {X}.
Arguments NoneE {X}.
Arguments OutOfFuel {X}.

Open Scope string_scope.

Definition parser (T : Type) :=
    list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | _, OutOfFuel => OutOfFuel
  | 0, _ =>
      OutOfFuel
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

(** A (step-indexed) parser that expects zero or more [p]s: *)

Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(** A parser that expects a given token, followed by [p]: *)

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

(** A parser that expects a particular token: *)

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

(*** ------------------------
     Copland Specific Parsing
     ------------------------
***)

Definition isIdTail := fun x => orb (isAlphaNum x) (isUnderscore x).

Local Instance str_eq_clasplit_evt : EqClass string :=
  { eqb:= String.eqb;
    eqb_eq := String.eqb_eq }.

Definition symbol_map := MapD string ID_Type.

Notation "'map' k 'to' v 'in' m" := (mapD_set m k v) (at level 200, no associativity).

Definition parseSymbol (xs : list token) (sm : symbol_map) 
                         : optionE (symbol_map * string * list token) :=
    match xs with
    | [] => NoneE "Expected identifier"
    | x::xs' => match (list_of_string x) with
                | nil => NoneE ("Illegal identifier: nil - is this possible?")
                | xh :: xt => if andb (isLowerAlpha xh) (forallb isIdTail xt) then
                                SomeE (sm, x, xs')
                              else 
                                NoneE ("Illegal Identifier: '" ++ x ++ "'")
                end
    end.

Definition str_to_nat (x : list ascii) : nat :=
  (fold_left 
    (fun n d => 10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
    x
    0
  ).


Definition string_to_IDType (s : string) : ID_Type. Admitted.
(* Definition nat_to_IDType (s : nat) : ID_Type. Admitted. *)


(* TODO: Need a better string -> digit converter *)
Definition parseDigits (xs : list token) (sm : symbol_map)
      : optionE (symbol_map * string * list token) :=
  match xs with
  | nil     => NoneE "Expected digits"
  | x::xs'  => if (forallb isDigit (list_of_string x))
                then 
                  let dig := string_to_IDType (String.string_of_list_ascii (list_of_string x)) in
                  SomeE ((map x to dig in sm), x, xs')
                else NoneE "Invalid digit sequence"
  end.
(* 
Example parseDigits1 : parseDigits (tokenize "01") map_empty 
= SomeE (
    (map "01" to 1 in map_empty), "01", []).
reflexivity. Qed.

Example parseDigits2 : parseDigits (tokenize "183 cow") map_empty
= SomeE ((map "183" to 183 in map_empty),"183", ["cow"]).
reflexivity. Qed.

Example parseDigits3 : parseDigits ["1"; "kim"; "2"; "ker"] map_empty
= SomeE ((map "1" to 1 in map_empty), "1", ["kim"; "2"; "ker"]).
reflexivity. Qed. *)

Definition parsePlace (xs : list token) (sm : symbol_map)
                      : optionE (symbol_map * string * list token) :=
  match xs with
  | nil => NoneE "Expected Place"
  | x::xs' => (* we need places to be either DIGITS or p + DIGITS *)
              match (list_of_string x) with
                | nil => NoneE ("Illegal place: nil - is this possible?")
                | xh :: xt => if andb (isLowerAlpha xh) (forallb isDigit xt) then
                              (* we are a p + DIGITS *)
                                let dig := string_to_IDType (String.string_of_list_ascii xt) in
                                SomeE ((map x to dig in sm), x, xs')
                              else if (forallb isDigit (xh :: xt)) then
                                (* we are completely a digit *)
                                let dig := string_to_IDType (String.string_of_list_ascii (list_of_string x)) in
                                SomeE ((map x to dig in sm), x, xs')
                              else 
                                NoneE ("Illegal Identifier: '" ++ x ++ "'")
                end
    end.

Definition spToStr (s : SP) :=
  match s with
  | ALL => "+"
  | NONE => "-"
  end.

Definition parserSoundASP 
  (p :  list token -> symbol_map
        -> (optionE (symbol_map * Term * list token))) 
  (val : string) 
  (a : ASP) : Prop :=
    forall s t (sm : symbol_map), 
    (s = val <-> p (s :: t) sm = SomeE (sm, (asp a), t))
    /\
    (s <> val <-> exists m, p (s :: t) sm = NoneE m).

Definition parseCopy (xs : list token) (sm : symbol_map)
                      : optionE (symbol_map * Term * list token) := 
  match xs with
  | nil => NoneE "Expected a copy"
  | h :: t => if (h =? "_") 
                then SomeE (sm, (asp CPY), t) 
                else NoneE "Invalid CPY"
  end.
  
Ltac qinv H := inversion H; subst; clear H.

Ltac soundParse :=
  split;
  repeat match goal with
  | |- context [?s = ?str <-> _] => split; intros H;
      try (subst; reflexivity); try (inversion H; destruct (String.eqb s str) eqn:E; [
        rewrite String.eqb_eq in E; assumption
        | 
        discriminate
    ])
  | |- context [?s <> ?str <-> _] => split; intros H; [
        unfold not in H; destruct (String.eqb s str) eqn:E; [
          simpl; rewrite String.eqb_eq in E; subst; exfalso; apply H; reflexivity
          |
          simpl; rewrite E; eexists; reflexivity
        ]
        |
        inversion H; inversion H0; destruct (String.eqb s str) eqn:E; [
          inversion H2
          |
          unfold not; intros; subst; inversion E
        ]
        ]
  end.

Lemma isCopySound : parserSoundASP parseCopy "_" CPY.
Proof.
  soundParse.
Qed.

(* TODO: Need to make guarantee that parseSymbol only consumes 1 token *)
Definition parseASPC (xs : list token) (sm : symbol_map)
                      : optionE (symbol_map * Term * list token) := 
    let sym1 := parseSymbol xs sm in
    match sym1 with
    | OutOfFuel => OutOfFuel
    | NoneE m => NoneE m
    | SomeE (sm', x',xs') => 
        let place := parsePlace xs' sm' in
        match place with
        | OutOfFuel => OutOfFuel
        | NoneE m => NoneE m
        | SomeE (sm'', x'',xs'') =>   
                  let sym2 := parseSymbol xs'' sm'' in
                  match sym2 with
                  | OutOfFuel => OutOfFuel
                  | NoneE m => NoneE m
                  | SomeE (sm''', x''',xs''') => 
                      match (mapD_get_value sm''' x'') with
                      (* TODO: Right now we FORCE the place to be digits because
                        the place is digits in Coq, we should find a way around this
                        though *)
                      | None => NoneE "Failed to find relevant symbol for ASPC"
                      | Some pNat =>
                          SomeE (sm''',
                            (asp (ASPC ALL EXTD (asp_paramsC (string_to_IDType x') nil pNat (string_to_IDType x''')))),
                            xs''')
                      end
                  end
        end
    end.

Definition parseSign (xs : list token) sm : optionE (symbol_map * Term * list token) := 
  match xs with
  | nil => NoneE "Expected a sign"
  | h :: t => if (h =? "!") 
                then SomeE (sm, (asp SIG), t) 
                else NoneE "Invalid SIGN"
  end.

Lemma isSignSound : parserSoundASP parseSign "!" SIG.
Proof.
  soundParse.
Qed.

Definition parseHash (xs : list token) sm : optionE (symbol_map * Term * list token) := 
  match xs with
  | nil => NoneE "Expected a hash"
  | h :: t => if (h =? "#") 
                then SomeE (sm, (asp HSH), t) 
                else NoneE "Invalid HASH"
  end.

Lemma isHashSound: parserSoundASP parseHash "#" HSH.
Proof.
    soundParse.
Qed.

Definition parseNull (xs : list token) sm : optionE (symbol_map * Term * list token) :=
  match xs with
  | nil => NoneE "Expected NULL"
  | h :: t => if (h =? "{}")
                then SomeE (sm, (asp NULL), t)
                else NoneE "Invalid Null"
  end.

Lemma isNullSound : parserSoundASP parseNull "{}" NULL.
Proof.
  soundParse.
Qed.

Definition parseASP (xs : list token) (sm : symbol_map)
                    : optionE (symbol_map * Term * list token) :=
    match xs with
    | nil   => NoneE "Expected ASP"
    | x::t  =>  
        match (parseNull xs sm) with
        | OutOfFuel => OutOfFuel
        | SomeE x' => SomeE x'
        | NoneE _ =>
            match (parseCopy xs sm) with
            | OutOfFuel => OutOfFuel
            | SomeE x'' => SomeE x''
            | NoneE _ =>
                match (parseASPC xs sm) with
                | OutOfFuel => OutOfFuel
                | SomeE x''' => SomeE x'''
                | NoneE _ =>
                    match (parseSign xs sm) with
                    | OutOfFuel => OutOfFuel
                    | SomeE x'''' => SomeE x''''
                    | NoneE _ =>
                        match (parseHash xs sm) with
                        | OutOfFuel => OutOfFuel
                        | SomeE x''''' => SomeE x'''''
                        | NoneE _ => NoneE "Expected an ASP"
                        end
                    end
                end
            end
        end
    end. 

Definition parseBranch (xs : list token) (prevT : Term) (sm : symbol_map)
                : optionE (symbol_map * (Term -> Term) * list token) :=
    match xs with
    | nil   => NoneE "Expected branch"
    | h::t  => (* we only check head, as this should be one contiguous token *)
                if (string_dec h "-<-")
                then SomeE (sm, fun t' => (bseq (NONE, NONE) prevT t'), t)
                else if (string_dec h "-<+")
                then SomeE (sm, fun t' => (bseq (NONE, ALL) prevT t'), t)
                else if (string_dec h "+<-")
                then SomeE (sm, fun t' => (bseq (ALL, NONE) prevT t'), t)
                else if (string_dec h "+<+")
                then SomeE (sm, fun t' => (bseq (ALL, ALL) prevT t'), t)
                else if (string_dec h "-~-")
                then SomeE (sm, fun t' => (bpar (NONE, NONE) prevT t'), t)
                else if (string_dec h "-~+")
                then SomeE (sm, fun t' => (bpar (NONE, ALL) prevT t'), t)
                else if (string_dec h "+~-")
                then SomeE (sm, fun t' => (bpar (ALL, NONE) prevT t'), t)
                else if (string_dec h "+~+")
                then SomeE (sm, fun t' => (bpar (ALL, ALL) prevT t'), t)
                else NoneE "Invalid branch"
    end.

Definition parseAT_Place (xs : list token) (sm : symbol_map)
                        : optionE (symbol_map * Plc * list token) :=
  (* here, we deal with the cases for @ place *)
  match xs with
  | nil => NoneE "Looking for @ place"
  | h :: t =>
      (* convert it to a list of string in case @ place or @place *)
      let lh := (list_of_string h) in
      if (Nat.eqb (String.length h) 1) 
      then (* it is likely @ place *)
        if (string_dec h "@")
        then (* found @, look for place in rem tokens*)
          match parsePlace t sm with
          | OutOfFuel => OutOfFuel
          | NoneE m => NoneE m
          | SomeE (sm', pStr, tks) =>
              match (map_get sm' pStr) with
              | None => NoneE "ERROR - Invalid Place in Map"
              | Some plc => 
                  SomeE (sm', plc, tks)
              end
          end
        else (* it was not @, *)
          NoneE "Expected @ symbol"
      else
        (* likely @place *)
        match lh with
        | nil => NoneE "Invalid token for AT Place"
        | h' :: t' =>
            (* expand to first char and tail *)
            if (Ascii.eqb h' "@")
            then (* found @, look for place in rem of token*)
              let firstTok : token := (string_of_list t') in
              match parsePlace (firstTok :: t) sm with
              | OutOfFuel => OutOfFuel
              | NoneE m => NoneE m
              | SomeE (sm', pStr, tks) =>
                  match (map_get sm' pStr) with
                  | None => NoneE "ERROR - Invalid Place in Map"
                  | Some plc => 
                      SomeE (sm', plc, tks)
                  end
              end
            else (* it was not @, *)
              NoneE "Expected @ symbol"
        end
  end.

Fixpoint parsePhrase (fuel : nat) (xs : list token) (sm : symbol_map)
              : optionE (symbol_map * Term * list token) :=
  (* we are using the left-recursive removed grammer now *)
match fuel with
| 0 => OutOfFuel
| S fuel' => 
  match xs with
  | nil     => NoneE "Expected phrase"
  | h::t  =>  (* We have tokens to work with *)
                (* try parsing an ASP *)
                match (parseASP xs sm) with
                | OutOfFuel => OutOfFuel
                | SomeE (sm', x',xs') => (* Parse the PHR' *)
                    match (parsePhrase' fuel' x' xs' sm') with
                    | OutOfFuel => OutOfFuel
                    | NoneE m => NoneE m
                    | SomeE (_, OutOfFuel, _ ) => OutOfFuel
                    | SomeE (sm', NoneE m,_) => (* It was empty *) 
                          SomeE (sm', x', xs')
                          (* NoneE m *)
                          (* SomeE (x',xs') *)
                    | SomeE (sm', SomeE x'', xs'') => SomeE (sm', x'', xs'')
                    end
                | NoneE m'  => (* try parsing ATT *)
                    match (parseATT fuel' xs sm) with
                    | OutOfFuel => OutOfFuel
                    | SomeE (sm', x'',xs'') => 
                        (* parsePhrase' fuel' x'' xs'' *)
                        match (parsePhrase' fuel' x'' xs'' sm') with
                        | OutOfFuel => OutOfFuel
                        | NoneE m => NoneE (m ++ ", " ++ m')
                        | SomeE (_, OutOfFuel, _ ) => OutOfFuel
                        | SomeE (sm', NoneE m,_) => (* It was empty *) 
                              SomeE (sm', x'',xs'')
                              (* NoneE (m ++ ", " ++ m') *)
                              (* let mT : list token := [m] in
                              SomeE (x'', (xs'' ++ mT)) *)
                        | SomeE (sm', SomeE x''', xs''') => SomeE (sm', x''', xs''')
                        end
                    | NoneE m'' => (* Try parsing parens *)
                        match (parseParens fuel' xs sm) with
                        | OutOfFuel => OutOfFuel
                        | SomeE (sm', x''', xs''') => 
                            (* parsePhrase' fuel' x''' xs''' *)
                            match (parsePhrase' fuel' x''' xs''' sm') with
                            | OutOfFuel => OutOfFuel
                            | NoneE m => NoneE m
                            | SomeE (_, OutOfFuel, _ ) => OutOfFuel
                            | SomeE (sm', NoneE _,_) => 
                                  (* It was empty *) SomeE (sm', x''',xs''')
                            | SomeE (sm', SomeE x'''', xs'''') => 
                                  SomeE (sm', x'''', xs'''')
                            end
                        | NoneE m''' => (* We actually failed*)
                                  NoneE ("Fail: " ++ m''' ++ ", " ++ m'' ++ ", " ++ m')
                        end
                    end
                end
  end
end
with parsePhrase' (fuel : nat) (prevT : Term) 
                  (xs : list token) (sm : symbol_map)
                  : optionE (symbol_map * (optionE Term) * list token) :=
  match fuel with
  | 0 => OutOfFuel
  | S (fuel') => 
      match xs with
      | nil => SomeE (sm, NoneE "Empty1", xs)
      (* SomeE ("",nil) (* NEED TO FIX, we should be able to parse no more*) *)
      | h :: t => if (string_dec h "->") 
                  then (* it is an arrow *)
                      match (parsePhrase fuel' t sm) with
                      | OutOfFuel => OutOfFuel
                      | NoneE m' => NoneE ("invalid arrow")
                      | SomeE (sm', x',xs') => 
                                  match (parsePhrase' fuel' (lseq prevT x') xs' sm') with
                                  | OutOfFuel => OutOfFuel
                                  | NoneE m'' => NoneE m''
                                  | SomeE (sm', NoneE m, _) => 
                                        SomeE (sm', SomeE (lseq prevT x'), xs')
                                  | SomeE (sm', x'',xs'') => SomeE (sm', x'', xs'')
                                  end
                      end
                  else (* try parse branch *)
                      match (parseBranch xs prevT sm) with
                      | OutOfFuel => OutOfFuel
                      | NoneE m' => SomeE (sm, NoneE "Empty2", xs) (* must be empty *)
                      | SomeE (sm', brnFn,xs') => 
                          match (parsePhrase fuel' xs' sm') with
                          | OutOfFuel => OutOfFuel
                          | NoneE m'' => NoneE m''
                          | SomeE (sm'', x'',xs'') => 
                                SomeE (sm'', (SomeE (brnFn x'')), xs'')
                          end
                      end
      end
  end
with parseATT (fuel : nat) (xs : list token) (sm : symbol_map)
              : optionE (symbol_map * Term * list token) :=
  match fuel with
  | 0 => OutOfFuel
  | S (fuel') => 
      match xs with
      | nil => NoneE "Expected @ plc PHR"
      | x :: xs' =>
          match (parseAT_Place xs sm) with
          | OutOfFuel => OutOfFuel
          | NoneE m => NoneE ("Failed to parseATT : ")
          | SomeE (sm', x',xs') => 
              (* we got out @ place now we need [phr] or phr*)
              match xs' with
              | nil => NoneE "Missing phrase after @ place"
              | h :: t =>
                  if (string_dec h "[")
                  then
                    (* we are in brackets *)
                    match (parsePhrase fuel' t sm') with
                    | OutOfFuel => OutOfFuel
                    | NoneE m => NoneE ("Invalid phrase after @ place (1) due to (" ++ m ++ "), ")
                    | SomeE (sm'', x'',xs'') => 
                        (* we have parsed the phrase, check for final brackets *)
                        match xs'' with
                        | nil => NoneE "Missing final brackets"
                        | h :: t => 
                            if (string_dec h "]")
                            then
                              SomeE (sm'', att x' x'', t)
                            else
                              NoneE "Invalid final brackets"
                        end
                    end
                  else
                    match (parsePhrase fuel' xs' sm') with
                    | OutOfFuel => OutOfFuel
                    | NoneE m => NoneE ("Invalid phrase after @ place (2) due to (" ++ m ++ "), ")
                    | SomeE (sm', x'',xs'') => SomeE (sm', att x' x'', xs'')
                    end
              end
          end
      end
  end
with parseParens (fuel : nat) (xs : list token) (sm : symbol_map) 
                  : optionE (symbol_map * Term * list token) :=
  match fuel with
  | 0 => OutOfFuel
  | S (fuel') => 
      match xs with
      | nil => NoneE "Missing parenthesis"
      | h :: t =>
          if (string_dec h "(")
          then
            (* we are in parens *)
            match (parsePhrase fuel' t sm) with
            | OutOfFuel => OutOfFuel
            | NoneE m => NoneE ("Invalid phrase within parens due to (" ++ m ++ "), ")
            | SomeE (sm', x'',xs'') => 
                (* we have parsed the phrase, check for final parens *)
                match xs'' with
                | nil => NoneE "Missing final parens"
                | h :: t => 
                    if (string_dec h ")")
                    then
                      SomeE (sm', x'', t)
                    else
                      NoneE "Invalid final parens"
                end
            end
          else
            NoneE "Missing parenthesis"
      end
  end
.

End CopParser.