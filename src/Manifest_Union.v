Require Import AbstractedTypes Term_Defs_Core Maps String
  Term_Defs Manifest_Admits EqClass ErrorStMonad_Coq
  Example_Phrases_Admits.

Require Import Manifest Manifest_Set EnvironmentM.

Require Import List.
Import ListNotations.

Definition manifest_set_union{A:Type} (s1:manifest_set A) (s2:manifest_set A) : manifest_set A.
Admitted.

Definition manifest_union (m1:Manifest) (m2:Manifest) : Manifest := 
    match (m1, m2) with 
    | ((Build_Manifest myPlc asps1 app_asps1 uuidPlcs1 pubKeyPlcs1 targPlcs1 myPol),
       (Build_Manifest _     asps2 app_asps2 uuidPlcs2 pubKeyPlcs2 targPlcs2 _    )) => 

       Build_Manifest
        myPlc 
        (manifest_set_union asps1 asps2)
        (manifest_set_union app_asps1 app_asps2)
        (manifest_set_union uuidPlcs1 uuidPlcs2)
        (manifest_set_union pubKeyPlcs1 pubKeyPlcs2)
        (manifest_set_union targPlcs1 targPlcs2)
        myPol
    end.

Definition environment_union (e1:EnvironmentM) (e2:EnvironmentM) : EnvironmentM. 
Admitted.