(*  Copland language definition.
    
   -Term(T):  Copland Phrase AST.
*)

From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Appraisal_Defs.
Require Import Term_Defs.
Require Import Anno_Term_Defs.
Require Import Maps.
Require Import EqClass.

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
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

Open Scope string_scope.

Definition parser (T : Type) :=
    list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
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

(* Adding a notation to match PARSEC from Haskell *)
Notation "' p <- e1 <|> e2" 
    := (match e1 with
        | SomeE p => e1
        | NoneE err => e2
        end) (right associativity, p pattern, at level 60, e1 at next level).

Definition isIdTail := fun x => orb (isAlphaNum x) (isUnderscore x).

Theorem weak_string_eqb_eq : forall x y : string,
  (x =? y) = true -> x = y.
Proof.
  apply String.eqb_eq.
Qed.

Instance str_eq_class : EqClass string :=
  { eqb:= String.eqb;
    eqb_leibniz := weak_string_eqb_eq }.

Definition symbol_map := MapD string nat.

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

Compute parseSymbol ["b1hello_bob";"world"; ","; "this"; "is";"a";"(";"simple";")";"test";"!";"var";"bob";";";"var";"b_b"; ";";"var";"";"icansay";"123"] map_empty % string.

(* TODO: Need a better string -> digit converter *)
Definition parseDigits (xs : list token) (sm : symbol_map)
      : optionE (symbol_map * string * list token) :=
  match xs with
  | nil     => NoneE "Expected digits"
  | x::xs'  => if (forallb isDigit (list_of_string x))
                then 
                  let dig := (fold_left
                                (fun n d =>
                                    10 * n + (nat_of_ascii d -
                                              nat_of_ascii "0"%char))
                                (list_of_string x)
                                0) in
                  SomeE ((map x to dig in sm), x, xs')
                else NoneE "Invalid digit sequence"
  end.

Example parseDigits1 : parseDigits (tokenize "01") map_empty 
= SomeE (
    (map "01" to 1 in map_empty), "01", []).
reflexivity. Qed.

Example parseDigits2 : parseDigits (tokenize "183 cow") map_empty
= SomeE ((map "183" to 183 in map_empty),"183", ["cow"]).
reflexivity. Qed.

Example parseDigits3 : parseDigits ["1"; "kim"; "2"; "ker"] map_empty
= SomeE ((map "1" to 1 in map_empty), "1", ["kim"; "2"; "ker"]).
reflexivity. Qed.

Definition parsePlace (xs : list token) (sm : symbol_map)
                      : optionE (symbol_map * string * list token) :=
  match xs with
  | nil => NoneE "Expected Place"
  | x::xs' => (* try parse symbol *)
              match (parseSymbol xs sm) with
              | SomeE x => SomeE x
              | NoneE m => (* try parse digits *)
                            match (parseDigits xs sm) with
                            | SomeE x' => SomeE x'
                            | NoneE m' => NoneE (m ++ m')
                            end
              end
  end. 

Definition aspToCopString (a : ASP) (sm : symbol_map): string :=
  match a with
  | NULL  => "{}"
  | CPY   => "_"
  | SIG   => "!"
  | HSH   => "#"
  | ASPC (asp_paramsC aId args plc tId) =>
      match (mapD_get_key sm plc) with
      | None => "ERROR: Could not locate symbol"
      | Some plcN =>
        aId ++ " " ++ plcN ++ " " ++ tId
      end
  end.


Example aspToCopString0 : aspToCopString (ASPC (asp_paramsC "hi" nil 102 "ker")) map_empty =
  "ERROR: Could not locate symbol". reflexivity. Qed.


Example aspToCopString1 : 
aspToCopString (ASPC (asp_paramsC "hi" nil 102 "ker")) (map "102" to 102 in mapD_empty) =
  "hi 102 ker". reflexivity. Qed.

Definition spToStr (s : SP) :=
  match s with
  | ALL => "+"
  | NONE => "-"
  end.

Fixpoint termToCopString (t : Term) (sm : symbol_map) : string :=
  match t with
  | asp a       => aspToCopString a sm
  | att p t     => match (mapD_get_key sm p) with
                   | None => "ERROR - Could not map place"
                   | Some pstr => "@" ++ pstr ++ " " ++ termToCopString t sm
                   end
  | lseq t1 t2  => termToCopString t1 sm ++ " -> " ++ termToCopString t2 sm
  | bseq (s1,s2) t1 t2 => 
    termToCopString t1 sm ++ " " ++ 
    spToStr s1 ++ "<" ++ spToStr s2 ++ " " ++ termToCopString t2 sm
  | bpar (s1,s2) t1 t2 =>
    termToCopString t1 sm ++ " " ++ spToStr s1 
    ++ "~" ++ spToStr s2 ++ " " ++ termToCopString t2 sm
  end.

Example termToCopString1 : termToCopString <{ @ 1 [ < "vc" 2 "sys" > ]}> (map "1" to 1 in (map "2" to 2 in map_empty))= "@1 vc 2 sys".
reflexivity. Qed.

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
    | NoneE m => NoneE m
    | SomeE (sm', x',xs') => 
        let place := parseDigits xs' sm' in
        match place with
        | NoneE m => NoneE m
        | SomeE (sm'', x'',xs'') =>   
                  let sym2 := parseSymbol xs'' sm'' in
                  match sym2 with
                  | NoneE m => NoneE m
                  | SomeE (sm''', x''',xs''') => 
                      match (map_get sm''' x'') with
                      | None => NoneE "Failed to find relevant symbol for ASPC"
                      | Some pNat =>
                          SomeE (sm''',
                            (asp (ASPC (asp_paramsC x' nil pNat x'''))),
                            xs''')
                      end
                  end
        end
    end.

Compute parseASPC (tokenize "p2 0 kim") map_empty.

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
        | SomeE x' => SomeE x'
        | NoneE _ =>
            match (parseCopy xs sm) with
            | SomeE x'' => SomeE x''
            | NoneE _ =>
                match (parseASPC xs sm) with
                | SomeE x''' => SomeE x'''
                | NoneE _ =>
                    match (parseSign xs sm) with
                    | SomeE x'''' => SomeE x''''
                    | NoneE _ =>
                        match (parseHash xs sm) with
                        | SomeE x''''' => SomeE x'''''
                        | NoneE _ => NoneE "Expected an ASP"
                        end
                    end
                end
            end
        end
    end. 

Compute parseASP (tokenize "hello 189 d_1").

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
      if (Nat.eqb (length h) 1) 
      then (* it is likely @ place *)
        if (string_dec h "@")
        then (* found @, look for place in rem tokens*)
          match parsePlace t sm with
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

Compute parseAT_Place (tokenize " @1029 cow ham cheese").

Fixpoint parsePhrase (fuel : nat) (xs : list token) (sm : symbol_map)
              : optionE (symbol_map * Term * list token) :=
  (* we are using the left-recursive removed grammer now *)
match fuel with
| 0 => NoneE "Out of fuel"
| S fuel' => 
  match xs with
  | nil     => NoneE "Expected phrase"
  | h::t  =>  (* We have tokens to work with *)
                (* try parsing an ASP *)
                match (parseASP xs sm) with
                | SomeE (sm', x',xs') => (* Parse the PHR' *)
                    match (parsePhrase' fuel' x' xs' sm') with
                    | NoneE m => NoneE m
                    | SomeE (sm', NoneE m,_) => (* It was empty *) 
                          SomeE (sm', x', xs')
                          (* NoneE m *)
                          (* SomeE (x',xs') *)
                    | SomeE (sm', SomeE x'', xs'') => SomeE (sm', x'', xs'')
                    end
                | NoneE m'  => (* try parsing ATT *)
                    match (parseATT fuel' xs sm) with
                    | SomeE (sm', x'',xs'') => 
                        (* parsePhrase' fuel' x'' xs'' *)
                        match (parsePhrase' fuel' x'' xs'' sm') with
                        | NoneE m => NoneE (m ++ ", " ++ m')
                        | SomeE (sm', NoneE m,_) => (* It was empty *) 
                              SomeE (sm', x'',xs'')
                              (* NoneE (m ++ ", " ++ m') *)
                              (* let mT : list token := [m] in
                              SomeE (x'', (xs'' ++ mT)) *)
                        | SomeE (sm', SomeE x''', xs''') => SomeE (sm', x''', xs''')
                        end
                    | NoneE m'' => (* Try parsing parens *)
                        match (parseParens fuel' xs sm) with
                        | SomeE (sm', x''', xs''') => 
                            (* parsePhrase' fuel' x''' xs''' *)
                            match (parsePhrase' fuel' x''' xs''' sm') with
                            | NoneE m => NoneE m
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
  | 0 => NoneE "Out of Fuel"
  | S (fuel') => 
      match xs with
      | nil => SomeE (sm, NoneE "Empty1", xs)
      (* SomeE ("",nil) (* NEED TO FIX, we should be able to parse no more*) *)
      | h :: t => if (string_dec h "->") 
                  then (* it is an arrow *)
                      match (parsePhrase fuel' t sm) with
                      | NoneE m' => NoneE ("invalid arrow")
                      | SomeE (sm', x',xs') => 
                                  match (parsePhrase' fuel' (lseq prevT x') xs' sm') with
                                  | NoneE m'' => NoneE m''
                                  | SomeE (sm', NoneE m, _) => 
                                        SomeE (sm', SomeE (lseq prevT x'), xs')
                                  | SomeE (sm', x'',xs'') => SomeE (sm', x'', xs'')
                                  end
                      end
                  else (* try parse branch *)
                      match (parseBranch xs prevT sm) with
                      | NoneE m' => SomeE (sm, NoneE "Empty2", xs) (* must be empty *)
                      | SomeE (sm', brnFn,xs') => 
                          match (parsePhrase fuel' xs' sm') with
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
  | 0 => NoneE "Out of fuel"
  | S (fuel') => 
      match xs with
      | nil => NoneE "Expected @ plc PHR"
      | x :: xs' =>
          match (parseAT_Place xs sm) with
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
  | 0 => NoneE "Out of fuel"
  | S (fuel') => 
      match xs with
      | nil => NoneE "Missing parenthesis"
      | h :: t =>
          if (string_dec h "(")
          then
            (* we are in parens *)
            match (parsePhrase fuel' t sm) with
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

Definition testPhr := "@1 kim 2 ker -> ! -<- @2 (vc 2 sys) -> !".
(* Definition testPhr2 := "@p1 kim p2 ker -> ! -<- ! -> @p2 (vc p2 sys) -> !".
Compute tokenize testPhr. *)

Definition transTestPhr := <{ @ 1 [< "kim" 2 "ker" > -> (!) -<- @ 2 [< "vc" 2 "sys"> -> !]]}>.

Print transTestPhr.
Compute parsePhrase 20 (tokenize "") map_empty.
Compute parsePhrase 20 (tokenize testPhr) map_empty.

(* 
Lemma parser_app : forall (n1 n2 : nat) (t1 t2 : Term) (s1 s2 xs1 xs2 : list token),
  parsePhrase n1 s1 = SomeE (t1, xs1) ->
  parsePhrase n2 s2 = SomeE (t2, xs2) ->
  exists n1, parsePhrase n1 (s1 ++ s2) = SomeE (t1, (List.app xs1 s2)).
Proof.
  intros.
   *)

Theorem prettyPrintParsable : forall (t : Term) p,
  exists n sm, 
    (forall v, mapD_get_key sm v = Some p) -> 
    parsePhrase n (tokenize (termToCopString t sm)) map_empty =
      SomeE (sm, t, nil).
Proof.
  intros.
  induction t.
  - simpl. induction a; simpl.
    * exists 2. simpl. exists map_empty. reflexivity.
    * exists 2. simpl. exists map_empty. reflexivity.
    * destruct a. exists 2.
      destruct p.
      ** exists (map "0" to 0 in map_empty).
         (* we cannot force a and t to not be space?! *)
         admit.
      ** (* invincible p value :( *) admit.
    * exists 2. simpl. exists map_empty. reflexivity.
    * exists 2. simpl. exists map_empty. reflexivity.
  - destruct IHt as [n' [sm' H]].
    simpl.
    exists (n' + 2). exists sm'. 
    simpl. 
    intros.
    rewrite H0.
    simpl.


Theorem parser_involutive: forall (t t1 : Term) sm rsm sm' rsm',
  exists n, parsePhrase n (tokenize (termToCopString t rsm')) sm rsm = SomeE (sm', rsm', t1, nil) ->
  termToCopString t = termToCopString t1.
Proof.
  intros t.
  induction t; intros.
  - destruct a.
    * exists 2. simpl. intros. qinv H. reflexivity.
    * exists 2. simpl. intros H. qinv H. reflexivity.
    * destruct a. destruct p.
      ** simpl.
      ** exists 2. destruct p. 
        *** destruct a.
          **** simpl. intros. discriminate.
          **** simpl. intros. 
  induction t.
  - simpl. destruct a. 
    * simpl. unfold tokenize. simpl. exists 10. simpl. reflexivity.
    * simpl. unfold tokenize. simpl. exists 10. reflexivity.
    * destruct a. admit. (* dies on computation? *)
    * simpl. unfold tokenize. simpl. exists 10. reflexivity.
    * simpl. unfold tokenize. simpl. exists 10. reflexivity.
  - induction p.
    * simpl. unfold tokenize. simpl. destruct IHt.
      exists (x + 2). simpl. admit.
    * admit.
  - simpl. unfold tokenize. simpl. destruct IHt1.
    destruct IHt2. exists (x + x0 + 2).
    simpl. admit.
  - simpl. destruct s.
  
Qed.




(* If we have a        (Sign, Hash) *)
Fixpoint checkSign_Hash (bb : (bool * bool)) (t : Term): (bool * bool) :=
    match t with
    | (asp a) =>
        match a with
        | SIG => let (s', h') := bb in if s' then (s', h') else (true, false)
        | HSH => let (s', _) := bb in (s', true)
        | _ => bb
        end
    | (att plc t)            => checkSign_Hash bb t
    | (lseq f sec)            => match (checkSign_Hash bb f) with
                                | (sf,hf) => if sf
                                                then (if hf 
                                                    then (true,true)
                                                    else (checkSign_Hash (sf,hf) sec))
                                                else (checkSign_Hash (sf,hf) sec)
                                end
    | (bseq (sp1,sp2) f sec) => match sp1 with
                                | ALL => match sp2 with
                                        | ALL => (* Check both*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (sf,hf) sec)
                                            end
                                        | NONE => (* Check only sp1 with above, reset below*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)    => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                | NONE => match sp2 with
                                        | ALL => (* Check only sp2 with above, reset below*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash bb sec)
                                            end
                                        | NONE => (* reset for both*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                end
    | (bpar (sp1,sp2) f sec) => match sp1 with
                                | ALL => match sp2 with
                                        | ALL => (* Check both*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (sf,hf) sec)
                                            end
                                        | NONE => (* Check only sp1 with above, reset below*)
                                            match (checkSign_Hash bb f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                | NONE => match sp2 with
                                        | ALL => (* Check only sp2 with above, reset below*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash bb sec)
                                            end
                                        | NONE => (* reset for both*)
                                            match (checkSign_Hash (false,false) f) with
                                            | (true, true)  => (true,true)
                                            | (sf,hf)       => (checkSign_Hash (false,false) sec)
                                            end
                                        end
                                end 
    end.

Example csh_test1 : checkSign_Hash (false,false) (lseq (asp SIG) (asp HSH)) = (true,true).
reflexivity. Qed.

Example csh_test2 : 
    checkSign_Hash (false,false) (lseq (asp SIG) (lseq (asp CPY) (asp HSH)))
    = (true,true).
simpl.
reflexivity. Qed.

Definition sign_hash_TypeCheck (t : Term) : @optionE Term :=
    match (checkSign_Hash (false,false) t) with
    | (true, true)  => NoneE "Failed typecheck"
    | (_,_)         => SomeE t
    end.

Example shTC1 : sign_hash_TypeCheck (lseq (asp SIG) (asp HSH)) = NoneE "Failed typecheck".
Proof. reflexivity. Qed.

Example shTC2 : sign_hash_TypeCheck (lseq (asp HSH) (asp SIG)) = SomeE (lseq (asp HSH) (asp SIG)).
reflexivity. Qed.

Lemma none_not_some : forall (t : Term),
    @NoneE Term "" = SomeE t -> False.
Proof.
    intros. discriminate.
Qed.

Lemma checkSH_lseq : forall (t1 t2 : Term) b0 b1,
    ((checkSign_Hash (false,false) t1) = (b0,b1) -> (b0 = true /\ b1 = true) -> (checkSign_Hash (false, false) (lseq t1 t2) = (true,true))) 
    /\
    ((checkSign_Hash (false,false) t1) = (b0,b1) -> (b0 <> true \/ b1 <> true) -> (checkSign_Hash (false, false) (lseq t1 t2) = (checkSign_Hash (b0, b1) t2))).
Proof.
    split; intros.
    * destruct H0; subst. simpl. rewrite H. reflexivity.
    * destruct H0.
        ** simpl. apply Bool.not_true_is_false in H0. subst. rewrite H. reflexivity.
        ** simpl. apply Bool.not_true_is_false in H0. 
            subst. rewrite H.
            destruct b0; reflexivity.
Qed.

Lemma T_impl_P : forall (P : Prop),
    (True -> P) -> P.
Proof.
    intros.
    apply H. apply I.
Qed.

Lemma att_injective_SH : forall p t,
    sign_hash_TypeCheck (att p t) = SomeE (att p t) ->
    sign_hash_TypeCheck t = SomeE t.
Proof.
    unfold sign_hash_TypeCheck.
    intros.
    induction t; simpl in *.
    - induction a; reflexivity.
    - destruct (checkSign_Hash (false,false) t).
        destruct b,b0; simpl in *; try discriminate; try reflexivity.
    - destruct (checkSign_Hash (false,false) t1) eqn:T1.
        destruct (checkSign_Hash (false,false) t2) eqn:T2.
        destruct b,b0,b1,b2; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.

        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
    - destruct (checkSign_Hash (false,false) t1) eqn:T1.
        destruct (checkSign_Hash (false,false) t2) eqn:T2.
        destruct b,b0,b1,b2; simpl in *; destruct s as [s1 s2]; destruct s1, s2; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.

        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
    - destruct (checkSign_Hash (false,false) t1) eqn:T1.
        destruct (checkSign_Hash (false,false) t2) eqn:T2.
        destruct b,b0,b1,b2; simpl in *; destruct s as [s1 s2]; destruct s1, s2; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (true,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.

        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,true) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
        * destruct (checkSign_Hash (false,false) t2) eqn:T2'.
            destruct b,b0; simpl in *; try discriminate; try reflexivity.
Qed.

Lemma termsub_refl : forall t t',
    t = t' ->
    term_sub t t' <-> term_sub t' t.
Proof.
    split; intros; subst; assumption.
Qed. 

Lemma att_term_sub_bijection : forall t t' p,
    (att p t) <> t' ->
    term_sub t' t <-> term_sub t' (att p t).
Proof.
    split; intros.
    - apply aatt_sub_annt. apply H0.
    - generalize dependent t. induction t'; intros.
        * qinv H0. apply H3.
        * qinv H0.
            ** (* very obviously false, (X ..) cannot be sub of X *)
                (* proving it different story *)
                exfalso. apply H. reflexivity.
            ** apply H3.
        * qinv H0. apply H3.
        * qinv H0. apply H3.
        * qinv H0. apply H3.
Qed.

End CopParser.