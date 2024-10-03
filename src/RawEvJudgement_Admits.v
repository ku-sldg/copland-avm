Require Import Term_Defs.

Require Import String.

Open Scope string_scope.

Definition ex_targJudgement_fun : RawEv -> string := 
    (fun _ => "SAMPLE JUDGEMENT STRING ONE").

Definition ex_targJudgement_fun' : RawEv -> string := 
    (fun _ => "SAMPLE JUDGEMENT STRING TWO").