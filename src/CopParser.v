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

Module CopParser.

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
unfold tokenize. simpl. reflexivity. Qed.

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

Definition parseSymbol (xs : list token)
                         : optionE (string * list token) :=
    match xs with
    | [] => NoneE "Expected identifier"
    | x::xs' => match (list_of_string x) with
                | nil => NoneE ("Illegal identifier: nil - is this possible?")
                | xh :: xt => if andb (isLowerAlpha xh) (forallb isIdTail xt) then
                                SomeE ("ID " ++ x, xs')
                              else 
                                NoneE ("Illegal Identifier: '" ++ x ++ "'")
                end
    end.

Compute parseSymbol ["b1hello_bob";"world"; ","; "this"; "is";"a";"(";"simple";")";"test";"!";"var";"bob";";";"var";"b_b"; ";";"var";"";"icansay";"123"] % string.

Definition parseDigits (xs : list token) : optionE (string * list token) :=
  match xs with
  | nil     => NoneE "Expected digits"
  | x::xs'  => if (forallb isDigit (list_of_string x))
                then SomeE ("DIG: " ++ x, xs')
                else NoneE "Invalid digit sequence"
  end.
  
Definition parsePlace (xs : list token) : optionE (string * list token) :=
  match xs with
  | nil => NoneE "Expected Place"
  | x::xs' => (* try parse symbol *)
              match (parseSymbol xs) with
              | SomeE x => SomeE x
              | NoneE m => (* try parse digits *)
                            match (parseDigits xs) with
                            | SomeE x' => SomeE x'
                            | NoneE m' => NoneE (m ++ m')
                            end
              end
  end.

Ltac soundParse :=
    intros s;
    match goal with
    | |- context [ s <> ?str <-> _] => 
                split; (* split and *)
                [ split; intros H; (* split bijection *)
                    [
                    rewrite <- String.eqb_neq in H;
                    destruct (String.eqb s str) eqn:E; auto; discriminate
                    |
                    apply String.eqb_neq; assumption
                    ]
                | split; intros H; [
                        subst; reflexivity
                        |
                        match goal with
                        | H : context [?x s = true ] |- _ => unfold x in H;
                                                            apply String.eqb_eq; assumption
                        end
                ]
                ]
    end.

Definition parserSound (p : string -> bool) (val : string) : Prop :=
    forall s, 
    (s <> val <-> p s = false)
    /\
    (s = val <-> p s = true).

Definition isNull (x : string) : bool :=
    x =? String "{" (String "}" EmptyString).

Lemma isNullSound : parserSound isNull "{}".
Proof.
    soundParse.
Qed.

Definition isCopy (x : string) : bool := (x =? String "_" EmptyString).

Lemma isCopySound : parserSound isCopy "_".
Proof.
    soundParse.
Qed.

Definition isSign (x : string) : bool := (x =? String "!" EmptyString).

Lemma isSignSound : parserSound isSign "!".
Proof.
    soundParse.
Qed.

Definition isHash (x : string) : bool := (x =? String "#" EmptyString).

Lemma isHashSound: parserSound isHash "#".
Proof.
    soundParse.
Qed.

(* TODO: Need to make guarantee that parseSymbol only consumes 1 token *)
Definition parseASPC (xs : list token) : optionE (string * list token) := 
    let sym1 := parseSymbol xs in
    match sym1 with
    | NoneE m => NoneE m
    | SomeE (x',xs') => 
        let place := parsePlace xs' in
        match place with
        | NoneE m => NoneE m
        | SomeE (x'',xs'') =>   let sym2 := parseSymbol xs'' in
                                match sym2 with
                                | NoneE m => NoneE m
                                | SomeE (x''',xs''') => 
                                        SomeE ("SPS sym1: " ++ x' ++ ", place: " ++ x'' ++ " , sym2: "++ x''',xs''')
                                end
        end
    end.

Definition token_str (x : token) : string := x.

Definition parseASP (xs : list token) : optionE (string * list token) :=
    match xs with
    | nil   => NoneE "Expected ASP"
    | x::t  => if (isNull x) then
                    SomeE ("NULL " ++ x, t)
                else if (isCopy x) then
                    SomeE ("COPY " ++ x, t)
                else if (isSign x) then
                    SomeE ("SIGN " ++ x, t)
                else if (isHash x) then
                    SomeE ("HASH " ++ x, t)
                else match (parseASPC (x::t)) with
                    | SomeE re  => SomeE re
                    | NoneE re  => NoneE (if string_dec re "" 
                                            then ("Invalid ASP '" ++ x ++ "'") 
                                            else re)
                    end
    end.

Compute parseASP (tokenize "hello bob d_1").

Definition parseBranch (xs : list token) : optionE (string * list token) :=
    match xs with
    | nil   => NoneE "Expected branch"
    | h::t  => (* we only check head, as this should be one contiguous token *)
                if (string_dec h "-<-")
                then SomeE ("BSEQ (NONE, NONE)", t)
                else if (string_dec h "-<+")
                then SomeE ("BSEQ (NONE, ALL)", t)
                else if (string_dec h "+<-")
                then SomeE ("BSEQ (ALL, NONE)", t)
                else if (string_dec h "+<+")
                then SomeE ("BSEQ (ALL,ALL)", t)
                else if (string_dec h "-~-")
                then SomeE ("BPAR (NONE, NONE)", t)
                else if (string_dec h "-~+")
                then SomeE ("BPAR (NONE, ALL)", t)
                else if (string_dec h "+~-")
                then SomeE ("BPAR (ALL, NONE)", t)
                else if (string_dec h "+~+")
                then SomeE ("BPAR (ALL,ALL)", t)
                else NoneE "Invalid branch"
    end.

Definition isSome {X : Type} (o : optionE X) : bool :=
    match o with
    | SomeE _ => true
    | _ => false
    end.

Ltac qinv H := inversion H; subst; clear H.

Definition parseAT_Place (xs : list token) : optionE (string * list token) :=
  (* here, we deal with the cases for @ place *)
  match xs with
  | nil => NoneE "Looking for @ place"
  | h :: t =>
      (* convert it to a list of string in case @ place or @place *)
      let lh := (list_of_string h) in
      if (eqb (length lh) 1) 
      then (* it is likely @ place *)
        if (string_dec h "@")
        then (* found @, look for place in rem tokens*)
          match (parsePlace t) with
          | NoneE m => NoneE m
          | SomeE (x',xs') => SomeE ("AT: " ++ x', t)
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
              match (parsePlace [string_of_list t']) with
              | NoneE m => NoneE m
              | SomeE (x',xs') => SomeE ("AT: " ++ x', t)
              end
            else (* it was not @, *)
              NoneE "Expected @ symbol"
        end
  end.

Compute parseAT_Place (tokenize " @$doug").

Fixpoint parsePhrase (fuel : nat) (xs : list token) : optionE (string * list token) :=
  (* we are using the left-recursive removed grammer now *)
match fuel with
| 0 => NoneE "Out of fuel"
| S fuel' => 
  match xs with
  | nil     => NoneE "Expected phrase"
  | h::t  =>  (* We have tokens to work with *)
                (* try parsing an ASP *)
                match (parseASP xs) with
                | SomeE (x',xs') => (* Parse the PHR' *)
                    match (parsePhrase' fuel' xs') with
                    | NoneE m => NoneE m
                    | SomeE (x'',xs'') => SomeE (x' ++ x'', xs'')
                    end
                | NoneE m'  => (* try parsing ATT *)
                    match parseATT fuel' xs with
                    | SomeE (x'',xs'') => 
                        match (parsePhrase' fuel' xs'') with
                        | NoneE m'' => NoneE (m' ++ m'')
                        | SomeE (x''',xs''') =>
                            SomeE (x'' ++ x''', xs''')
                        end
                    | NoneE m'' => (* Try parsing parens *)
                        match (parseParens fuel' xs) with
                        | SomeE (x''', xs''') => 
                            match parsePhrase' fuel' xs''' with
                            | NoneE m'' => NoneE m''
                            | SomeE (x'''',xs'''') => SomeE (x''' ++ x'''', xs'''')
                            end
                        | NoneE m''' => (* We actually failed*)
                                  NoneE ("Fail: " ++ m''')
                        end
                    end
                end
  end
end
with parsePhrase' (fuel : nat) (xs : list token) : optionE (string * list token) :=
  match fuel with
  | 0 => NoneE "Out of Fuel"
  | S (fuel') => 
      match xs with
      | nil => SomeE ("",nil)
      | h :: t => if (string_dec h "->") 
                  then (* it is an arrow *)
                      match (parsePhrase fuel' t) with
                      | NoneE m' => NoneE ("invalid arrow")
                      | SomeE (x',xs') => 
                                  match (parsePhrase' fuel' xs') with
                                  | NoneE m'' => NoneE m''
                                  | SomeE (x'',xs'') => 
                                      SomeE (" ARR " ++ x' ++ x'', xs'')
                                  end
                      end
                  else (* try parse branch *)
                      match (parseBranch xs) with
                      | NoneE m' => SomeE ("",xs) (* must be empty *)
                      | SomeE (x',xs') => 
                          match (parsePhrase fuel' xs') with
                          | NoneE m'' => NoneE m''
                          | SomeE (x'',xs'') => SomeE ("BRN " ++ x' ++ x'', xs'')
                          end
                      end
      end
  end
with parseATT (fuel : nat) (xs : list token) : optionE (string * list token) :=
  match fuel with
  | 0 => NoneE "Out of fuel"
  | S (fuel') => 
      match xs with
      | nil => NoneE "Expected @ plc PHR"
      | x :: xs' =>
          match (parseAT_Place xs) with
          | NoneE m => NoneE ("Failed to parseATT : ")
          | SomeE (x',xs') => 
              (* we got out @ place now we need [phr] or phr*)
              match xs' with
              | nil => NoneE "Missing phrase after @ place"
              | h :: t =>
                  if (string_dec h "[")
                  then
                    (* we are in brackets *)
                    match (parsePhrase fuel' t) with
                    | NoneE m => NoneE ("Invalid phrase after @ place")
                    | SomeE (x'',xs'') => 
                        (* we have parsed the phrase, check for final brackets *)
                        match xs'' with
                        | nil => NoneE "Missing final brackets"
                        | h :: t => 
                            if (string_dec h "]")
                            then
                              SomeE (x' ++ x'', t)
                            else
                              NoneE "Invalid final brackets"
                        end
                    end
                  else
                    match (parsePhrase fuel' xs') with
                    | NoneE m => NoneE ("Invalid phrase after @ place")
                    | SomeE (x'',xs'') => SomeE (x' ++ x'', xs'')
                    end
              end
          end
      end
  end
with parseParens (fuel : nat) (xs : list token) : optionE (string * list token) :=
  match fuel with
  | 0 => NoneE "Out of fuel"
  | S (fuel') => 
      match xs with
      | nil => NoneE "Missing parenthesis"
      | h :: t =>
          if (string_dec h "(")
          then
            (* we are in parens *)
            match (parsePhrase fuel' t) with
            | NoneE m => NoneE ("Invalid phrase within parens " ++ m)
            | SomeE (x'',xs'') => 
                (* we have parsed the phrase, check for final parens *)
                match xs'' with
                | nil => NoneE "Missing final parens"
                | h :: t => 
                    if (string_dec h ")")
                    then
                      SomeE ("PARENS : (" ++ x'' ++ ")", t)
                    else
                      NoneE "Invalid final parens"
                end
            end
          else
            NoneE "Missing parenthesis"
      end
  end
.

Definition testPhr := "@p1 kim p2 ker -> ! -<- ! -> @p2 (vc p2 sys) -> !".
Compute tokenize testPhr.

Compute parsePhrase 20 (tokenize testPhr).
Compute parsePhrase 20 (tokenize "").
Compute parseAT_Place (tokenize testPhr).







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

Inductive ind_check_sh : (bool * bool) -> Term -> (bool * bool) -> Prop :=
| csh_asp_sig_t : forall bs bh, (* true case, sign seen previously, no update *)
                    bs = true -> 
                    bh = false -> 
                    ind_check_sh (true, false) (asp SIG) (true, false)
| csh_asp_sig_f : forall bs bh, (* false case sign not seen previously *)
                    bs = false ->
                    ind_check_sh (bs,bh) (asp SIG) (bs,bh)
| csh_asp_hsh   : forall bh, (* case, sign cannot be seen previously *)
                    ind_check_sh (false, bh) (asp HSH) (false, bh)
| csh_asp_other : forall a bs bh, (* other asp's just pass along *)
                    a <> HSH /\ a <> SIG -> 
                    (* TODO: Technically think we allow (true,true) now, but not reachable? *)
                    ind_check_sh (bs,bh) (asp a) (bs,bh)
| 

Example ind_check_sh1 : ind_check_sh (true, false) (asp SIG) (true, false).
apply (csh_asp_sig_t true false); reflexivity. Qed.

Example ind_check_sh2 : ~ (ind_check_sh (true, false) (asp HSH) (true, true)).
(* we cannot generate a failing program *)
unfold not. intros.
qinv H. Qed.

Example ind_check_sh3 : forall b1 b2, (ind_check_sh (b1, b2) (asp CPY) (b1,b2)).
constructor.
split; intros H; discriminate.
Qed.

    match t with
    | (asp a) =>
        match a with
        | SIG => let (s', h') := bb in if s' then (s', h') else (true, false)
        | HSH => let (s', _) := bb in (s', true)
        | _ => (false, false)
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

Inductive Option {X : Type} : Type :=
| Some {X} (n : X)
| None.

Definition sign_hash_TypeCheck (t : Term) : @Option Term :=
    match (checkSign_Hash (false,false) t) with
    | (true, true)  => None
    | (_,_)         => Some t
    end.

Example shTC1 : sign_hash_TypeCheck (lseq (asp SIG) (asp HSH)) = None.
Proof. reflexivity. Qed.

Example shTC2 : sign_hash_TypeCheck (lseq (asp HSH) (asp SIG)) = Some (lseq (asp HSH) (asp SIG)).
reflexivity. Qed.

Lemma none_not_some : forall (t : Term),
    @None Term = Some t -> False.
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
    sign_hash_TypeCheck (att p t) = Some (att p t) ->
    sign_hash_TypeCheck t = Some t.
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

Theorem checkSH_impl_not_hash_sig_term : forall (t : Term),
    sign_hash_TypeCheck t = Some t ->
    not_hash_sig_term t.
Proof.
    intros t H.
    unfold sign_hash_TypeCheck in H. 
    unfold not_hash_sig_term.
    induction t; simpl in *; unfold not in *.
    - admit.
    - intros t' Ht' Htsub. 
      destruct (checkSign_Hash (false,false) t) eqn:E.
      destruct b,b0; simpl in *; try discriminate.
      * assert (Htemp : @Some Term Term t = Some t). {
          reflexivity.
      } apply (IHt Htemp (att p t)). 
        qinv Htsub.
        ** assumption.
    Restart.
    intros t H.
    induction t; unfold not_hash_sig_term in *; unfold not in *; simpl in *; intros.
    - qinv H1. qinv H0. destruct H1 as [e [H1 [H2 H3]]].
        qinv H1.
    - pose proof (att_injective_SH p t). apply H2 in H. 
        apply (IHt H t').
        * apply H0.
        * pose proof (att_term_sub_bijection t t' p).
            apply H3.
            ** unfold not. intros. (* possible they equal, but violate hash_sig *)
                subst. qinv H0.
                destruct H4 as [e [He1 [He2 He3]]].
                discriminate.
            ** apply H1.
    - 

Theorem not_hash_sig_term_impl_typeCheckPass: 
    forall (t : Term),
        not_hash_sig_term t -> sign_hash_TypeCheck t = Some t.
Proof.
    intros t H.
    unfold not_hash_sig_term in H.
    induction t.
    - (* basic asp *)
        induction a; reflexivity.
    - (* basic att *)
        unfold sign_hash_TypeCheck in *.
        pose proof (none_not_some t) as NTF.
        destruct (checkSign_Hash (false,false) (att p t)) eqn:E;
        destruct (checkSign_Hash (false,false) t) eqn:E'.
        destruct b,b0; try reflexivity.
        destruct b1,b2; simpl in *.
        * exfalso. apply NTF.
            apply IHt.
            intros.
            specialize H with t'.
            unfold not. intros. 
            apply H. apply H0.
            apply aatt_sub_annt. apply H1.
        * rewrite E in E'. discriminate.
        * rewrite E in E'. discriminate.
        * rewrite E in E'. discriminate.
    - (* lseq t1 t2*)
        unfold sign_hash_TypeCheck in *.
        destruct (checkSign_Hash (false,false) t1) eqn:Et1.
        destruct (checkSign_Hash (false,false) t2) eqn:Et2.
        (* We should be able to construct Lt1t2 from previous *)
        (* destruct (checkSign_Hash (false,false) (lseq t1 t2)) eqn:Lt1t2. *)
        (* destruct b3,b4; try reflexivity. *)
        destruct b,b0; destruct b1,b2; try (
            (* kill t1 cases *)
            exfalso;
            apply (none_not_some (t1));
            apply IHt1; intros;
            specialize H with t';
            unfold not; intros;
            apply H; [apply H0 | apply alseq_subl_annt; apply H1]
        ); try (
            (* kill t2 cases *)
            exfalso;
            apply (none_not_some (t2));
            apply IHt2; intros;
            specialize H with t';
            unfold not; intros;
            apply H; [apply H0 | apply alseq_subr_annt; apply H1]
        ).
        * pose proof (checkSH_lseq t2 t1 true false) as Hsh.
            destruct Hsh as [_ Hsh].
            apply Hsh in Et2.
            ** 
            ** 
        * qinv Lt1t2. rewrite Et1 in H1.
            (* even if we start in true we never see HSH to double true *)
            admit.
        * qinv Lt1t2. rewrite Et1 in H1.
            (* this is very tricky, seems like it should truly be false *)
            admit.
        * qinv Lt1t2. rewrite Et1 in H1.
            (* never see HSH *)
            admit.
        * qinv Lt1t2. rewrite Et1 in H1.
            (* tricky case, seems like should fail *)
            admit.
        * rewrite <- Et1 in Et2. qinv Lt1t2.
            rewrite Et1 in H1.
            admit.


        (* either works *)
        * exfalso. 
            apply (none_not_some (t2)).
            apply IHt2. unfold not. intros.
            specialize H with t'.
            apply H.
            ** apply H0.
            ** apply alseq_subr_annt. apply H1.
        (* only t1 works *)
        * exfalso. 
            apply (none_not_some (t1)).
            apply IHt1. intros.
            specialize H with t'.
            unfold not. intros.
            apply H.
            ** apply H0.
            ** apply alseq_subl_annt. apply H1.
        (* only t1 works *)
        * exfalso. 
            apply (none_not_some (t1)).
            apply IHt1. intros.
            specialize H with t'.
            unfold not. intros.
            apply H.
            ** apply H0.
            ** apply alseq_subl_annt. apply H1.
        * 

    
Qed.


End CopParser.