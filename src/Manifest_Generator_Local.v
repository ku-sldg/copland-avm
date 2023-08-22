Require Import Term_Defs_Core Params_Admits Manifest Executable_Dec
               Example_Phrases_Admits Example_Phrases Eqb_Evidence
               Executable_Defs_Prop.

Require Import EqClass Maps StructTactics.

Require Export EnvironmentM.

Require Import List.
Import ListNotations.

Fixpoint add_to_list {A : Type} `{EqClass A} (l : list A) (v : A) : list A :=
  match l with
  | nil => v :: nil
  | h :: t => if (eqb h v) then (h :: t) else h :: (add_to_list t v)
  end.


Fixpoint generate_manifest' (t : Term) (p : Plc) 
    (m : Manifest) : Manifest :=
  match t with
  | asp a =>
      (* Only update manifest of myself *)
      if (eqb p m.(my_abstract_plc))
      then
        match a with
        | NULL => m
        | CPY => m
        | ASPC _ _ (asp_paramsC aspid args targp targid) =>
            {|
              my_abstract_plc := m.(my_abstract_plc) ;

              asps := add_to_list (m.(asps)) aspid ;
              uuidPlcs := m.(uuidPlcs) ;
              pubKeyPlcs := m.(pubKeyPlcs) ;
              targetPlcs := add_to_list (m.(targetPlcs)) targp ;
              policy := m.(policy) ;
            |}
        | SIG =>
            {|
              my_abstract_plc := m.(my_abstract_plc) ;

              asps := add_to_list (m.(asps)) sig_aspid ;
              uuidPlcs := m.(uuidPlcs) ;
              pubKeyPlcs := m.(pubKeyPlcs) ;
              targetPlcs := m.(targetPlcs) ;
              policy := m.(policy) ;
            |}
        | HSH =>
            {|
              my_abstract_plc := m.(my_abstract_plc) ;

              asps := add_to_list (m.(asps)) hsh_aspid ;
              uuidPlcs := m.(uuidPlcs) ;
              pubKeyPlcs := m.(pubKeyPlcs) ;
              targetPlcs := m.(targetPlcs) ;
              policy := m.(policy) ;
            |}
        | ENC p =>
            {|
              my_abstract_plc := m.(my_abstract_plc) ;

              asps := add_to_list (m.(asps)) enc_aspid ;
              uuidPlcs := m.(uuidPlcs) ;
              pubKeyPlcs := add_to_list (m.(pubKeyPlcs)) p ;
              targetPlcs := m.(targetPlcs) ;
              policy := m.(policy) ;
            |}
        end
      else m
  | att p' t' =>
      (* generate_manifest' t' p' *)
      ({|
        my_abstract_plc := m.(my_abstract_plc) ;

        asps := m.(asps) ;
        uuidPlcs := add_to_list (m.(uuidPlcs)) p' ;
        pubKeyPlcs := m.(pubKeyPlcs) ;
        targetPlcs := m.(targetPlcs) ;
        policy := m.(policy) ;
      |})
  | lseq t1 t2 =>
      generate_manifest' t2 p (generate_manifest' t1 p m)
  | bseq _ t1 t2 =>
      generate_manifest' t2 p (generate_manifest' t1 p m)
  | bpar _ t1 t2 =>
      generate_manifest' t2 p (generate_manifest' t1 p m)
  end.

Definition generate_manifest (t : Term) (p : Plc) :=
  generate_manifest' t p (
    {|
      my_abstract_plc := p ;

      asps := empty_Manifest.(asps) ;
      uuidPlcs := empty_Manifest.(uuidPlcs) ;
      pubKeyPlcs := empty_Manifest.(pubKeyPlcs) ;
      targetPlcs := empty_Manifest.(targetPlcs) ;
      policy := empty_Manifest.(policy) ;
    |}
  ).