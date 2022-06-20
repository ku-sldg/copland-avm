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

Definition parseSymbol (xs : list token)
                         : optionE (string * list token) :=
    match xs with
    | [] => NoneE "Expected identifier"
    | x::xs' => match (list_of_string x) with
                | nil => NoneE ("Illegal identifier: nil - is this possible?")
                | xh :: xt => if andb (isLowerAlpha xh) (forallb isIdTail xt) then
                                SomeE (x, xs')
                              else 
                                NoneE ("Illegal Identifier: '" ++ x ++ "'")
                end
    end.

Compute parseSymbol ["b1hello_bob";"world"; ","; "this"; "is";"a";"(";"simple";")";"test";"!";"var";"bob";";";"var";"b_b"; ";";"var";"";"icansay";"123"] % string.

(* TODO: Need a better string -> digit converter *)
Definition parseDigits (xs : list token) : optionE (nat * list token) :=
  match xs with
  | nil     => NoneE "Expected digits"
  | x::xs'  => if (forallb isDigit (list_of_string x))
                then SomeE ((fold_left
                                (fun n d =>
                                    10 * n + (nat_of_ascii d -
                                              nat_of_ascii "0"%char))
                                (list_of_string x)
                                0), xs')
                else NoneE "Invalid digit sequence"
  end.

Example parseDigits1 : parseDigits (tokenize "01") = SomeE (1, []).
reflexivity. Qed.

Example parseDigits2 : parseDigits (tokenize "183 cow") = SomeE (183, ["cow"]).
reflexivity. Qed.

Example parseDigits3 : parseDigits ["1"; "kim"; "2"; "ker"] = SomeE (1, ["kim"; "2"; "ker"]).
reflexivity. Qed.

(*   
We are leaving this out for now because frankly Coq only allows NATs as places

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
  end. *)

Definition parsePlace (xs : list token) : optionE (Plc * list token) :=
  match xs with
  | nil => NoneE "Expected Place"
  | x::xs' =>  (* try parse digits *) parseDigits xs
  end. 

Example parsePlace1 : parseDigits ["1"; "kim"; "2"; "ker"] = SomeE (1, ["kim"; "2"; "ker"]).
reflexivity. Qed.

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
(* 
Definition parserSoundASP 
  (p : (xs : list token) : (optionE (ASP * list token))) 
  (val : string) 
  (a : ASP) : Prop :=
    forall s, 
    (s <> val <-> p s = false)
    /\
    (s = val <-> p s = true). *)
(* 
Definition parseNull (xs : list token) : optionE (ASP * list token) := 
  match xs with
  | nil => NoneE "Expected a null"
  | h :: t => if (h =? "{}") 
                then SomeE (NULL, t) 
                else NoneE "Invalid NULL"
  end.

Lemma isNullSound : parserSound isNull "{}".
Proof.
    soundParse.
Qed. *)

Definition parseCopy (xs : list token) : optionE (ASP * list token) := 
  match xs with
  | nil => NoneE "Expected a copy"
  | h :: t => if (h =? "_") 
                then SomeE (CPY, t) 
                else NoneE "Invalid CPY"
  end.
(* 
Lemma isCopySound : parserSound isCopy "_".
Proof.
    soundParse.
Qed. *)

(* TODO: Need to make guarantee that parseSymbol only consumes 1 token *)
Definition parseASPC (xs : list token) : optionE (ASP * list token) := 
    let sym1 := parseSymbol xs in
    match sym1 with
    | NoneE m => NoneE m
    | SomeE (x',xs') => 
        let place := parseDigits xs' in
        match place with
        | NoneE m => NoneE m
        | SomeE (x'',xs'') =>   let sym2 := parseSymbol xs'' in
                                match sym2 with
                                | NoneE m => NoneE m
                                | SomeE (x''',xs''') => 
                                        SomeE ((ASPC (asp_paramsC x' nil x'' x''')),xs''')
                                end
        end
    end.

Example parseASPC1 : parseASPC (tokenize "p2 0 kim") = 
  SomeE (ASPC (asp_paramsC "p2" nil 0 "kim"), nil).
  reflexivity. Qed.

Definition parseSign (xs : list token) : optionE (ASP * list token) := 
  match xs with
  | nil => NoneE "Expected a sign"
  | h :: t => if (h =? "!") 
                then SomeE (SIG, t) 
                else NoneE "Invalid SIGN"
  end.
(* 
Lemma isSignSound : parserSound parseSign "!".
Proof.
    soundParse.
Qed. *)


Definition parseHash (xs : list token) : optionE (ASP * list token) := 
  match xs with
  | nil => NoneE "Expected a hash"
  | h :: t => if (h =? "#") 
                then SomeE (HSH, t) 
                else NoneE "Invalid HASH"
  end.
(* 
Lemma isHashSound: parserSound isHash "#".
Proof.
    soundParse.
Qed. *)

Definition parseNull (xs : list token) : optionE (ASP * list token) :=
  match xs with
  | nil => NoneE "Expected NULL"
  | h :: t => if (h =? "{}")
                then SomeE (NULL, t)
                else NoneE "Invalid Null"
  end.

Definition parseASP (xs : list token) : optionE (Term * list token) :=
    match xs with
    | nil   => NoneE "Expected ASP"
    | x::t  =>  
        match (parseNull xs) with
        | SomeE (x',x'') => SomeE (asp x', x'')
        | NoneE _ =>
            match (parseCopy xs) with
            | SomeE (x',x'') => SomeE (asp x', x'')
            | NoneE _ =>
                match (parseASPC xs) with
                | SomeE (x', x'') => SomeE (asp x', x'')
                | NoneE _ =>
                    match (parseSign xs) with
                    | SomeE (x', x'') => SomeE (asp x', x'')
                    | NoneE _ =>
                        match (parseHash xs) with
                        | SomeE (x', x'') => SomeE (asp x', x'')
                        | NoneE _ => NoneE "Expected an ASP"
                        end
                    end
                end
            end
        end
    end. 

Compute parseASP (tokenize "hello 189 d_1").
Example parseASP1 : parseASP (tokenize "hello 189 d_1") = SomeE (<{ < "hello" 189 "d_1" > }>, nil).
reflexivity. Qed.

Definition parseBranch (xs : list token) (prevT : Term) 
                : optionE ((Term -> Term) * list token) :=
    match xs with
    | nil   => NoneE "Expected branch"
    | h::t  => (* we only check head, as this should be one contiguous token *)
                if (string_dec h "-<-")
                then SomeE (fun t' => (bseq (NONE, NONE) prevT t'), t)
                else if (string_dec h "-<+")
                then SomeE (fun t' => (bseq (NONE, ALL) prevT t'), t)
                else if (string_dec h "+<-")
                then SomeE (fun t' => (bseq (ALL, NONE) prevT t'), t)
                else if (string_dec h "+<+")
                then SomeE (fun t' => (bseq (ALL, ALL) prevT t'), t)
                else if (string_dec h "-~-")
                then SomeE (fun t' => (bpar (NONE, NONE) prevT t'), t)
                else if (string_dec h "-~+")
                then SomeE (fun t' => (bpar (NONE, ALL) prevT t'), t)
                else if (string_dec h "+~-")
                then SomeE (fun t' => (bpar (ALL, NONE) prevT t'), t)
                else if (string_dec h "+~+")
                then SomeE (fun t' => (bpar (ALL, ALL) prevT t'), t)
                else NoneE "Invalid branch"
    end.

Ltac qinv H := inversion H; subst; clear H.

Definition parseAT_Place (xs : list token) : optionE (Plc * list token) :=
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
          parsePlace t
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
              parsePlace ( firstTok :: t)
            else (* it was not @, *)
              NoneE "Expected @ symbol"
        end
  end.

Compute parseAT_Place (tokenize " @1029 cow ham cheese").

Fixpoint parsePhrase (fuel : nat) (xs : list token) : optionE (Term * list token) :=
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
                    match parsePhrase' fuel' x' xs' with
                    | NoneE m => NoneE m
                    | SomeE (NoneE m,_) => (* It was empty *) 
                          SomeE (x', xs')
                          (* NoneE m *)
                          (* SomeE (x',xs') *)
                    | SomeE (SomeE x'', xs'') => SomeE (x'', xs'')
                    end
                | NoneE m'  => (* try parsing ATT *)
                    match parseATT fuel' xs with
                    | SomeE (x'',xs'') => 
                        (* parsePhrase' fuel' x'' xs'' *)
                        match parsePhrase' fuel' x'' xs'' with
                        | NoneE m => NoneE (m ++ ", " ++ m')
                        | SomeE (NoneE m,_) => (* It was empty *) 
                              SomeE (x'',xs'')
                              (* NoneE (m ++ ", " ++ m') *)
                              (* let mT : list token := [m] in
                              SomeE (x'', (xs'' ++ mT)) *)
                        | SomeE (SomeE x''', xs''') => SomeE (x''', xs''')
                        end
                    | NoneE m'' => (* Try parsing parens *)
                        match (parseParens fuel' xs) with
                        | SomeE (x''', xs''') => 
                            (* parsePhrase' fuel' x''' xs''' *)
                            match parsePhrase' fuel' x''' xs''' with
                            | NoneE m => NoneE m
                            | SomeE (NoneE _,_) => (* It was empty *) SomeE (x''',xs''')
                            | SomeE (SomeE x'''', xs'''') => SomeE (x'''', xs'''')
                            end
                        | NoneE m''' => (* We actually failed*)
                                  NoneE ("Fail: " ++ m''' ++ ", " ++ m'' ++ ", " ++ m')
                        end
                    end
                end
  end
end
with parsePhrase' (fuel : nat) (prevT : Term) (xs : list token) 
                                  : optionE ((optionE Term) * list token) :=
  match fuel with
  | 0 => NoneE "Out of Fuel"
  | S (fuel') => 
      match xs with
      | nil => SomeE (NoneE "Empty1", xs)
      (* SomeE ("",nil) (* NEED TO FIX, we should be able to parse no more*) *)
      | h :: t => if (string_dec h "->") 
                  then (* it is an arrow *)
                      match (parsePhrase fuel' t) with
                      | NoneE m' => NoneE ("invalid arrow")
                      | SomeE (x',xs') => 
                                  match (parsePhrase' fuel' (lseq prevT x') xs') with
                                  | NoneE m'' => NoneE m''
                                  | SomeE (NoneE m, _) => SomeE (SomeE (lseq prevT x'), xs')
                                  | SomeE (x'',xs'') => SomeE (x'', xs'')
                                  end
                      end
                  else (* try parse branch *)
                      match (parseBranch xs prevT) with
                      | NoneE m' => SomeE (NoneE "Empty2", xs) (* must be empty *)
                      | SomeE (brnFn,xs') => 
                          match (parsePhrase fuel' xs') with
                          | NoneE m'' => NoneE m''
                          | SomeE (x'',xs'') => SomeE ((SomeE (brnFn x'')), xs'')
                          end
                      end
      end
  end
with parseATT (fuel : nat) (xs : list token) : optionE (Term * list token) :=
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
                    | NoneE m => NoneE ("Invalid phrase after @ place (1) due to (" ++ m ++ "), ")
                    | SomeE (x'',xs'') => 
                        (* we have parsed the phrase, check for final brackets *)
                        match xs'' with
                        | nil => NoneE "Missing final brackets"
                        | h :: t => 
                            if (string_dec h "]")
                            then
                              SomeE (att x' x'', t)
                            else
                              NoneE "Invalid final brackets"
                        end
                    end
                  else
                    match (parsePhrase fuel' xs') with
                    | NoneE m => NoneE ("Invalid phrase after @ place (2) due to (" ++ m ++ "), ")
                    | SomeE (x'',xs'') => SomeE (att x' x'', xs'')
                    end
              end
          end
      end
  end
with parseParens (fuel : nat) (xs : list token) : optionE (Term * list token) :=
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
            | NoneE m => NoneE ("Invalid phrase within parens due to (" ++ m ++ "), ")
            | SomeE (x'',xs'') => 
                (* we have parsed the phrase, check for final parens *)
                match xs'' with
                | nil => NoneE "Missing final parens"
                | h :: t => 
                    if (string_dec h ")")
                    then
                      SomeE (x'', t)
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
Example testPhr1 : parsePhrase 20 (tokenize testPhr) 
  = SomeE (transTestPhr, []).
  reflexivity. Qed.

Print transTestPhr.
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