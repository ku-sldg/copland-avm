Require Import Term_Defs Example_Phrases_Pre_Admits.

Require Import List.
Import ListNotations.


Definition example_phrase_p2_appraise : Term := 
  <{
    @ P1 [
      (<< attest1_id P1 sys >> +<+ << attest2_id P1 sys >>) ] 
  }>.


