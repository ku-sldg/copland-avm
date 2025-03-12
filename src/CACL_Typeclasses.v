Require Import ID_Type EqClass Maps.
Require Import CACL_Defs JSON JSON_Core.

Require Import List.
Import ListNotations.


Definition eqb_CACL_Permission (a1 a2 : CACL_Permission)  : bool := 
    match a1 with 
    | CACL_Read => 
        match a2 with 
        | CACL_Read => true 
        | _ => false 
        end 
    | CACL_Write => 
        match a2 with 
        | CACL_Write => true 
        | _ => false 
        end 
    | CACL_Invoke => 
        match a2 with 
        | CACL_Invoke => true 
        | _ => false 
        end
    end.

(** Admitted Lemmas relating boolean to propositional equality for 
    CACL_Permission *)
Lemma eqb_eq_CACL_Permission: forall i1 i2,
    eqb_CACL_Permission i1 i2 = true <-> i1 = i2.
Proof.
    split;
        intros;
        destruct i1; destruct i2; 
        unfold eqb_CACL_Permission in *;
        try congruence;
        try eauto.
Qed.

Global Instance EqClassCACL_Permission `{H : EqClass ID_Type} : EqClass CACL_Permission := {
  eqb := eqb_CACL_Permission ;
  eqb_eq := eqb_eq_CACL_Permission
}.

Definition STR_CACL_Access : string := "CACL_Access".
Definition cacl_read_name_constant : string := "CACL_Read".
Definition cacl_write_name_constant : string := "CACL_Write".
Definition cacl_invoke_name_constant : string := "CACL_Invoke".

Definition CACL_Permission_to_JSON (t : CACL_Permission) : JSON := 
  match t with
  | CACL_Read => constructor_to_JSON STR_CACL_Access cacl_read_name_constant []
  | CACL_Write => constructor_to_JSON STR_CACL_Access cacl_write_name_constant []
  | CACL_Invoke => constructor_to_JSON STR_CACL_Access cacl_invoke_name_constant []
  end.

Definition CACL_Permission_from_JSON_map : Map string (JSON -> (ResultT CACL_Permission string)) := 
  [(cacl_read_name_constant, 
    constructor_from_JSON STR_CACL_Access (fun _ => resultC CACL_Read));
    (cacl_write_name_constant, 
    constructor_from_JSON STR_CACL_Access (fun _ => resultC CACL_Write));
    (cacl_invoke_name_constant, 
    constructor_from_JSON STR_CACL_Access (fun _ => resultC CACL_Invoke))].

Definition CACL_Permission_from_JSON (js : JSON) : ResultT CACL_Permission string :=
  from_JSON_gen STR_CACL_Access CACL_Permission_from_JSON_map js.

Global Instance jsonifiable_CACL_Permission : Jsonifiable CACL_Permission.
  eapply Build_Jsonifiable with 
    (to_JSON := CACL_Permission_to_JSON)
    (from_JSON := CACL_Permission_from_JSON).
  intuition; simpl in *.
  
  unfold CACL_Permission_to_JSON.
  unfold CACL_Permission_from_JSON.
  break_match;
  eapply from_JSON_gen_constructor_to_JSON_works;
  unfold CACL_Permission_from_JSON_map; try reflexivity.
Defined.

Global Instance Jsonifiable_CACL_Access `{Jsonifiable ID_Type, Jsonifiable CACL_Permission} : Jsonifiable CACL_Access.
eapply Build_Jsonifiable with 
  (to_JSON := pair_to_JSON)
  (from_JSON := pair_from_JSON).
simpl_json.
Defined.

Open Scope string_scope.

Global Instance Stringifiable_CACL_Permission : Stringifiable CACL_Permission :=
  {
    to_string := fun b => 
                  match b with 
                  | CACL_Read =>   "CACL_Read" 
                  | CACL_Write =>  "CACL_Write"
                  | CACL_Invoke => "CACL_Invoke"
                  end;
    from_string := fun s => 
                     match s with
                     | "CACL_Read" =>   resultC CACL_Read
                     | "CACL_Write" =>  resultC CACL_Write
                     | "CACL_Invoke" => resultC CACL_Invoke
                     | _ => errC "Not a CACL_Access"
                     end;
    canonical_stringification := fun b =>
                                   match b with
                                   | CACL_Read => eq_refl
                                   | CACL_Write => eq_refl
                                   | CACL_Invoke => eq_refl
                                   end;
  }.


(*


Global Instance Jsonifiable_list_CACL_Access `{Jsonifiable CACL_Permission} : Jsonifiable (list CACL_Access).
eapply Build_Jsonifiable with 
(to_JSON := map_serial_serial_to_JSON(* list_CACL_Access_to_JSON *))
(from_JSON := map_serial_serial_from_JSON (* list_CACL_Access_from_JSON *)).
intuition; induction a; simpl in *; intuition; eauto;
repeat (try break_match; simpl in *; subst; eauto; try congruence);
try rewrite canonical_jsonification in *; 
try rewrite canonical_stringification in *; 
repeat find_injection; simpl in *; 
try find_rewrite; eauto; try congruence.
Defined.


Global Instance Jsonifiable_CACL_Policy `{Stringifiable ID_Type, EqClass ID_Type, Jsonifiable CACL_Permission, Jsonifiable (list CACL_Access)}  : Jsonifiable CACL_Policy.
eapply Build_Jsonifiable with 
  (to_JSON := map_serial_serial_to_JSON)
  (from_JSON := map_serial_serial_from_JSON).
  intuition; induction a; simpl in *; intuition; eauto;
  repeat (try break_match; simpl in *; subst; eauto; try congruence);
  try rewrite canonical_jsonification in *; 
  try rewrite canonical_stringification in *; 
  repeat find_injection; simpl in *; 
  try find_rewrite; eauto; try congruence.
Defined.

*)

Definition eqb_CACL_Access `{H : EqClass ID_Type} (a1 a2 : CACL_Access)  : bool := 
    eqbPair a1 a2.

(** Admitted Lemmas relating boolean to propositional equality for 
   ASP ID and PARAMS *)
Lemma eqb_eq_CACL_Access: forall `{H : EqClass ID_Type} i1 i2,
    eqb_CACL_Access i1 i2 = true <-> i1 = i2.
Proof.
    split.
    -
        intros.
        unfold eqb_CACL_Access in *.
        eapply pair_eqb_eq; eauto.
    -
        intros.
        unfold eqb_CACL_Access in *.
        eapply pair_eqb_eq; eauto.
Qed.

Global Instance EqClassCACL_Access `{H : EqClass ID_Type} : EqClass CACL_Access := {
  eqb := eqb_CACL_Access ;
  eqb_eq := eqb_eq_CACL_Access
}.