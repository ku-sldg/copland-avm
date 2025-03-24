(* The Main interface for JSON that exports its sub-properties *)

Require Export JSON_Type JSON_Admits ResultT StructTactics.
Require Import List String Maps Stringifiable EqClass ErrorStringConstants.
Import ListNotations.
Import ResultNotation.

(* The JSONIFIABLE Class *)
Class Jsonifiable (A : Type) :=
  {
    to_JSON : A -> JSON;
    from_JSON : JSON -> ResultT A string;
    canonical_jsonification : forall (a : A), 
      from_JSON (to_JSON a) = resultC a
  }.

Ltac simpl_json :=
  unfold res_bind in *; simpl in *; intuition;
  repeat (try rewrite canonical_jsonification in *;
    try rewrite canonical_stringification in *;
    simpl in *; intuition).

Ltac solve_json := 
  simpl_json; try congruence;
  match goal with
  | |- resultC ?x = resultC ?y => 
    destruct y; simpl in *; subst; eauto
  end.

(* The JSONIFIABLE Class *)

Open Scope string_scope.

Definition JSON_get_Object (key : string) (js : JSON) : ResultT JSON string :=
  match js with
  | JSON_Object m => 
      match map_get key m with
      | Some v => resultC v 
      | None => errC (errStr_json_key_not_found key js) 
      end
  | _ => errC (errStr_json_wrong_type key js)
  end.

Definition JSON_get_Array (key : string) (js : JSON) : ResultT (list JSON) string :=
  match JSON_get_Object key js with
  | resultC (JSON_Array v) => resultC v
  | resultC _ => errC (errStr_json_wrong_type key js)
  | _ => errC (errStr_json_key_not_found key js)
  end.

Definition JSON_get_string (key : string) (js : JSON) : ResultT string string :=
  match JSON_get_Object key js with
  | resultC (JSON_String v) => resultC v
  | resultC _ => errC (errStr_json_wrong_type key js)
  | _ => errC (errStr_json_key_not_found key js)
  end.

Definition JSON_get_bool (key : string) (js : JSON) : ResultT bool string :=
  match (JSON_get_Object key js) with
  | resultC (JSON_Boolean v) => resultC v
  | resultC _ => errC (errStr_json_wrong_type key js)
  | _ => errC (errStr_json_key_not_found key js)
  end.

(* The Pair JSONIFIABLE Class *)
Definition str_pair_to_JSON {A B : Type} `{Stringifiable A, Stringifiable B} (v : (A * B)) : JSON :=
  JSON_Array [JSON_String (to_string (fst v)); JSON_String (to_string (snd v))].

Definition str_pair_from_JSON {A B : Type} `{Stringifiable A, Stringifiable B} (js : JSON) : ResultT (A * B) string :=
  match js with
  | JSON_Array [JSON_String a; JSON_String b] =>
    a <- from_string a ;;
    b <- from_string b ;;
    resultC (a, b)
  | _ => errC (errStr_json_from_pair)
  end.

Global Instance Jsonifiable_str_pair {A B : Type} `{Stringifiable A, Stringifiable B} : Jsonifiable (A * B).
eapply Build_Jsonifiable with 
  (to_JSON := str_pair_to_JSON)
  (from_JSON := str_pair_from_JSON).
simpl_json.
Defined.


Definition pair_to_JSON {A B : Type} `{Jsonifiable A, Jsonifiable B} (v : (A * B)) : JSON :=
  JSON_Array [(to_JSON (fst v)); (to_JSON (snd v))].

Definition pair_from_JSON {A B : Type} `{Jsonifiable A, Jsonifiable B} (js : JSON) : ResultT (A * B) string :=
  match js with
  | JSON_Array [a; b] =>
      match (from_JSON a), (from_JSON b) with
      | resultC a, resultC b => resultC (a, b)
      | _, _ => errC errStr_json_to_pair
      end
  | _ => errC errStr_json_to_pair
  end.

Global Instance Jsonifiable_pair {A B : Type} `{Jsonifiable A, Jsonifiable B} : Jsonifiable (A * B).
eapply Build_Jsonifiable with 
  (to_JSON := pair_to_JSON)
  (from_JSON := pair_from_JSON).
simpl_json.
Defined.

Global Instance jsonifiable_bool : Jsonifiable bool :=
  {
    to_JSON   := fun b => JSON_Boolean b ;
    from_JSON := fun js => 
                    match js with 
                    | JSON_Boolean b => resultC b 
                    | _ => errC (errStr_json_wrong_type "bool" js)
                    end;
    canonical_jsonification := fun b => 
                               match b with 
                               | true => eq_refl 
                               | _ => eq_refl 
                               end 
  }.


(* The List JSONIFIABLE Class *)

Definition map_serial_serial_to_JSON {A B : Type} `{Stringifiable A, Stringifiable B, EqClass A} (m : Map A B) : JSON :=
  JSON_Object (
    map (fun '(k, v) => (to_string k, JSON_String (to_string v))) m).

Definition map_serial_serial_from_JSON {A B : Type} `{Stringifiable A, Stringifiable B, EqClass A} (js : JSON) : ResultT (Map A B) string :=
  match js with
  | JSON_Object m => 
      result_map 
        (fun '(k, v) => 
          match v with
          | JSON_String v' =>
            k' <- from_string k ;;
            v' <- from_string v' ;;
            resultC (k', v')
          | _ => errC (errStr_map_from_json)
          end) m
  | _ => errC (errStr_map_from_json)
  end.

Lemma canonical_jsonification_map_serial_serial : forall {A B} `{Stringifiable A, Stringifiable B, EqClass A} (m : Map A B),
  map_serial_serial_from_JSON (map_serial_serial_to_JSON m) = resultC m.
Proof.
  intuition.
  induction m; simpl in *; eauto.
  repeat (try break_match; 
    subst; simpl in *; 
    try find_rewrite; 
    try find_injection; try congruence);
  repeat rewrite canonical_stringification in *;
  try congruence;
  repeat find_injection; eauto.
Qed.

Global Instance jsonifiable_map_serial_serial (A B : Type) `{Stringifiable A, EqClass A, Stringifiable B} : Jsonifiable (Map A B) :=
  {
    to_JSON   := map_serial_serial_to_JSON;
    from_JSON := map_serial_serial_from_JSON;
    canonical_jsonification := canonical_jsonification_map_serial_serial;
  }.

Global Instance jsonifiable_map_serial_json (A B : Type) `{Stringifiable A, EqClass A, Jsonifiable B} : Jsonifiable (Map A B).
eapply Build_Jsonifiable with (
  to_JSON := (fun m => JSON_Object (
                      map (fun '(k, v) => 
                            (to_string k, to_JSON v)
                          ) m))) 
  (from_JSON := (fun js =>   
                    match js with
                    | JSON_Object m => 
                        result_map 
                          (fun '(k, v) => 
                            k' <- from_string k ;;
                            v' <- from_JSON v ;;
                            resultC (k', v')) m
                    | _ => errC (errStr_map_from_json)
                    end));
intuition; induction a; simpl in *; intuition; eauto;
repeat (try break_match; simpl in *; subst; eauto; try congruence);
try rewrite canonical_jsonification in *; 
try rewrite canonical_stringification in *; 
repeat find_injection; simpl in *; 
try find_rewrite; eauto; try congruence.
Defined.

Close Scope string_scope.

(* Definition JSON_to_string_map {B : Type} `{Jsonifiable B} (js : JSON) 
    : ResultT (Map string B) string :=

Definition JSON_to_string_string_map {B : Type} `{Stringifiable B} (js : JSON) 
    : ResultT (Map string B) string :=

Global Instance jsonifiable_string_map (A : Type) `{Jsonifiable A} : Jsonifiable (Map string A) :=
  {
    to_JSON := string_map_to_JSON;
    from_JSON := JSON_to_string_map
  }. *)

(* Global Instance jsonifiable_id_map (A : Type) `{Jsonifiable A} : Jsonifiable (Map ID_Type A) :=
  {
    to_JSON := (fun m => string_map_to_JSON (id_map_to_string_map m));
    from_JSON := (fun js => 
                    match JSON_to_string_map js with
                    | errC e => errC e
                    | resultC m => string_map_to_id_map m
                    end)
  }.

Fixpoint id_B_map_to_string_map {B : Type} `{Stringifiable ID_Type, Stringifiable B} (m : Map ID_Type B) : Map string string :=
  match m with
  | [] => []
  | (k, v) :: m' => (to_string k, to_string v) :: (id_B_map_to_string_map m')
  end.

Fixpoint string_map_to_id_B_map {B : Type} `{Stringifiable ID_Type, Stringifiable B} (m : Map string string) : ResultT (Map ID_Type B) string :=
  match m with
  | [] => resultC []
  | (k, v) :: m' => 
    match (from_string k), (from_string v) with
    | resultC k', resultC v' => 
      match (string_map_to_id_B_map m') with
      | errC e => errC e
      | resultC m'' => resultC ((k', v') :: m'')
      end
    | _, _ => errC "Error in string_map_to_id_B_map"%string
    end
  end.

Global Instance jsonifiable_id_map_Stringifiables (A : Type) `{Stringifiable A} : Jsonifiable (Map ID_Type A) :=
  {
    to_JSON := (fun m => string_string_map_to_JSON (id_B_map_to_string_map m));
    from_JSON := (fun js => 
                    match JSON_to_string_string_map js with
                    | errC e => errC e
                    | resultC m => string_map_to_id_B_map m
                    end)
  }. *)

Fixpoint map_flatten {A B C : Type} `{EqClass A, EqClass B} 
    (m : Map (A * B) C) : list (A * B * C) :=
  match m with
  | [] => []
  | ((k1, k2), v) :: m' => (k1,k2,v) :: map_flatten m'
  end.

Fixpoint result_map_pairs {A B C : Type} `{EqClass A, EqClass B} (f : JSON -> ResultT ((A * B) * C) string) (l : list JSON)
    : ResultT (Map (A * B) C) string :=
  match l with
  | [] => resultC []
  | h :: t => 
      match f h with
      | errC e => errC e
      | resultC ((k1, k2), v) => 
          match result_map_pairs f t with
          | errC e => errC e
          | resultC m' => resultC (((k1, k2), v) :: m')
          end
      end
  end.

(* Definition map_pair_to_InnerJSON_string {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Stringifiable C} (m : Map (A * B) C) : list JSON :=
  List.map (fun '(k1, k2, v) => JSON_Array [JSON_String (to_string k1); JSON_String (to_string k2); JSON_String (to_string v)]) (map_flatten m).

Definition InnerJson_string_to_map_pair {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Stringifiable C} (js : list JSON) 
    : ResultT (Map (A * B) C) string :=
  result_map_pairs 
    (fun js' => 
        match js' with
        | JSON_Array [JSON_String k1; JSON_String k2; JSON_String v] =>
          match (from_string k1), (from_string k2), (from_string v) with
          | resultC k1, resultC k2, resultC v => resultC ((k1, k2), v)
          | _, _, _ => errC errStr_json_to_map
          end
        | _ => errC errStr_json_to_map
        end) js. *)

(* Definition map_pair_to_InnerJSON {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Jsonifiable C} (m : Map (A * B) C) : list InnerJSON :=
  List.map (fun '(k1, k2, v) => InJSON_Array [InJSON_String (to_string k1); InJSON_String (to_string k2); InJSON_Object (to_JSON v)]) (map_flatten m).

Definition InnerJson_to_map_pair {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Jsonifiable C} (js : list InnerJSON) 
    : ResultT (Map (A * B) C) string :=
  result_map_pairs 
    (fun js' => 
        match js' with
        | InJSON_Array [InJSON_String k1; InJSON_String k2; InJSON_Object v] =>
          match (from_string k1), (from_string k2), (from_JSON v) with
          | resultC k1, resultC k2, resultC v => resultC ((k1, k2), v)
          | _, _, _ => errC errStr_json_to_map
          end
        | _ => errC errStr_json_to_map
        end) js. *)