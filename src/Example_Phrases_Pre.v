(* Example phrases.  Here the "Pre" qualifier in the filename is due to a quirk in extracted code 
    dependencies that requires these definitions (used to statically configure inline appraisal) 
    to appear before others. *) 

Require Import Term_Defs Example_Phrases_Pre_Admits.

Require Import List.
Import ListNotations.

Open Scope cop_ent_scope.

Definition mysig := asp SIG.

Definition sub1 : Term := 
  <{ << attest1_id P1 sys >> +<+ (mysig) }>.

Definition example_phrase_p2_appraise : Term := 
  <{
    @ P1 [ sub1 ]

    (*
      (<< attest1_id P1 sys >> +<+ (mysig)(* << attest2_id P1 sys >> *)) ] 
      *)
  }>.

Close Scope cop_ent_scope.


