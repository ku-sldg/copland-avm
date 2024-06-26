(* The Main interface for JSON that exports its sub-properties *)

Require Export JSON_Type JSON_Admits ResultT.
Require Import List String Maps ErrorStringConstants AbstractedTypes.
Import ListNotations.

(* The JSONIFIABLE Class *)
Class Jsonifiable (A : Type) :=
  {
    to_JSON : A -> JSON;
    from_JSON : JSON -> ResultT A string;
    (* canonical_serialization
      : forall (js : JSON) (a : A), to_JSON a = js <-> (from_JSON js = resultC a); *)
  }.

Definition JSON_get_JSON (key : string) (js : JSON) : ResultT JSON string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_Object v => resultC v
          | _ => errC errStr_json_get_json_not_a_json
          end
      | None => errC errStr_json_get_json_key_not_found
      end
  end.

Definition JSON_get_Array (key : string) (js : JSON) : ResultT (list InnerJSON) string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_Array v => resultC v
          | _ => errC errStr_json_get_array_not_an_array
          end
      | None => errC errStr_json_get_array_key_not_found
      end
  end.

Definition JSON_get_string (key : string) (js : JSON) : ResultT string string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_String v => resultC v
          | _ => errC errStr_json_get_string_not_a_string
          end
      | None => errC errStr_json_get_string_key_not_found
      end
  end.

Definition JSON_get_bool (key : string) (js : JSON) : ResultT bool string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_Boolean v => resultC v
          | _ => errC errStr_json_get_bool_not_a_bool
          end
      | None => errC errStr_json_get_bool_key_not_found
      end
  end.

(* Lemma canonical_serialization_string : forall (js : JSON) (a : string), 
  JSON_String a = js <-> (resultC (JSON_to_string js) = @resultC _ string a).
Proof.
  setoid_rewrite canonical_serialization_json_string; intuition; eauto.
  - rewrite H; eauto. 
  - inversion H; eauto. 
Qed. *)
Open Scope string_scope.

Definition JSON_PAIR_FST := "PAIR_FST".
Definition JSON_PAIR_SND := "PAIR_SND".

(* The Pair JSONIFIABLE Class *)
Global Instance jsonifiable_serializable_pair (A B : Type) `{Serializable A, Serializable B} : Jsonifiable (A * B) :=
  {
    to_JSON := (fun '(a, b) => 
        JSON_Object [
          (JSON_PAIR_FST, InJSON_String (to_string a));
          (JSON_PAIR_SND, InJSON_String (to_string b))
        ]);
    from_JSON := (fun js => 
                    let '(JSON_Object m) := js in
                    match (JSON_get_string JSON_PAIR_FST js), (JSON_get_string JSON_PAIR_SND js) with
                    | resultC l, resultC r =>
                      match (from_string l), (from_string r) with
                      | resultC l, resultC r => resultC (l, r)
                      | _, _ => errC errStr_json_to_pair
                      end
                    | _, _ => errC errStr_json_to_pair
                    end)
  }.
Close Scope string_scope.
(* Lemma canonical_serialization_id_type : forall (js : JSON) (a : ID_Type), 
  JSON_String (ID_Type_to_string a) = js <-> (match js with | JSON_String s => string_to_ID_Type s | _ => errC errStr_json_to_id_type end = @resultC _ string a).
Proof.
  intuition; simpl in *.
  - pose proof (canonical_serialization_string js (ID_Type_to_string a)); intuition.
    inversion H0.
    rewrite H3.
    pose proof (canonical_string_id_type (ID_Type_to_string a) a); intuition.
  - pose proof (canonical_string_id_type (JSON_to_string js) a).
    intuition.
    rewrite H0.
    pose proof (canonical_serialization js (JSON_to_string js)).
    simpl in *; intuition.
Qed. *)

(* Global Instance jsonifiable_ID_type : Jsonifiable ID_Type :=
  {
    to_JSON := (fun v => JSON_String (ID_Type_to_string v));
    from_JSON := (fun v => 
                    match v with
                    | JSON_String s => string_to_ID_Type s
                    | _ => errC errStr_json_to_id_type
                    end);
    (* canonical_serialization := canonical_serialization_id_type *)
  }. *)

Definition string_map_to_JSON {B : Type} `{Jsonifiable B} (m : MapC string B) : JSON :=
  JSON_Object (map_map (fun x => InJSON_Object (to_JSON x)) m).

Definition string_string_map_to_JSON {B : Type} `{Serializable B} (m : MapC string B) : JSON :=
  JSON_Object (map_map (fun x => InJSON_String (to_string x)) m).

Definition JSON_to_string_map {B : Type} `{Jsonifiable B} (js : JSON) 
    : ResultT (MapC string B) string :=
  match js with
  | JSON_Object m => 
      result_map 
        (fun '(k, v) => 
            match v with
            | InJSON_Object v' =>
              match (from_JSON v') with
              | errC e => errC e
              | resultC v' => resultC (k, v')
              end
            | _ => errC errStr_json_to_map
            end) m
  end.

Definition JSON_to_string_string_map {B : Type} `{Serializable B} (js : JSON) 
    : ResultT (MapC string B) string :=
  match js with
  | JSON_Object m => 
      result_map 
        (fun '(k, v) => 
            match v with
            | InJSON_String v' =>
              match (from_string v') with
              | errC e => errC e
              | resultC v' => resultC (k, v')
              end
            | _ => errC errStr_json_to_map
            end) m
  end.

Global Instance jsonifiable_string_map (A : Type) `{Jsonifiable A} : Jsonifiable (MapC string A) :=
  {
    to_JSON := string_map_to_JSON;
    from_JSON := JSON_to_string_map
  }.

Global Instance jsonifiable_id_map (A : Type) `{Jsonifiable A} : Jsonifiable (MapC ID_Type A) :=
  {
    to_JSON := (fun m => string_map_to_JSON (id_map_to_string_map m));
    from_JSON := (fun js => 
                    match JSON_to_string_map js with
                    | errC e => errC e
                    | resultC m => string_map_to_id_map m
                    end)
  }.

Fixpoint id_B_map_to_string_map {B : Type} `{Serializable ID_Type, Serializable B} (m : MapC ID_Type B) : MapC string string :=
  match m with
  | [] => []
  | (k, v) :: m' => (to_string k, to_string v) :: (id_B_map_to_string_map m')
  end.

Fixpoint string_map_to_id_B_map {B : Type} `{Serializable ID_Type, Serializable B} (m : MapC string string) : ResultT (MapC ID_Type B) string :=
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

Global Instance jsonifiable_id_map_serializables (A : Type) `{Serializable A} : Jsonifiable (MapC ID_Type A) :=
  {
    to_JSON := (fun m => string_string_map_to_JSON (id_B_map_to_string_map m));
    from_JSON := (fun js => 
                    match JSON_to_string_string_map js with
                    | errC e => errC e
                    | resultC m => string_map_to_id_B_map m
                    end)
  }.

Fixpoint map_flatten {A B C : Type} `{EqClass A, EqClass B} 
    (m : MapC (A * B) C) : list (A * B * C) :=
  match m with
  | [] => []
  | ((k1, k2), v) :: m' => (k1,k2,v) :: map_flatten m'
  end.

Definition map_pair_to_InnerJSON {A B C : Type} `{Serializable A, EqClass A, EqClass B, Serializable B, Jsonifiable C} (m : MapC (A * B) C) : list InnerJSON :=
  List.map (fun '(k1, k2, v) => InJSON_Array [InJSON_String (to_string k1); InJSON_String (to_string k2); InJSON_Object (to_JSON v)]) (map_flatten m).

Fixpoint result_map_pairs {A B C : Type} `{EqClass A, EqClass B} (f : InnerJSON -> ResultT ((A * B) * C) string) (l : list InnerJSON)
    : ResultT (MapC (A * B) C) string :=
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

Definition InnerJson_to_map_pair {A B C : Type} `{Serializable A, EqClass A, EqClass B, Serializable B, Jsonifiable C} (js : list InnerJSON) 
    : ResultT (MapC (A * B) C) string :=
  result_map_pairs 
    (fun js' => 
        match js' with
        | InJSON_Array [InJSON_String k1; InJSON_String k2; InJSON_Object v] =>
          match (from_string k1), (from_string k2), (from_JSON v) with
          | resultC k1, resultC k2, resultC v => resultC ((k1, k2), v)
          | _, _, _ => errC errStr_json_to_map
          end
        | _ => errC errStr_json_to_map
        end) js.