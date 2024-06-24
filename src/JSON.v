(* The Main interface for JSON that exports its sub-properties *)

Require Export JSON_Type JSON_Admits ResultT StringT.
Require Import Maps ErrorStringConstants AbstractedTypes.

Class Jsonifiable (A : Type) :=
  {
    to_JSON : A -> JSON;
    from_JSON : JSON -> ResultT A StringT;
    (* canonical_serialization
      : forall (js : JSON) (a : A), to_JSON a = js <-> (from_JSON js = resultC a); *)
  }.

(* Lemma canonical_serialization_stringT : forall (js : JSON) (a : StringT), 
  JSON_String a = js <-> (resultC (JSON_to_stringT js) = @resultC _ StringT a).
Proof.
  setoid_rewrite canonical_serialization_json_stringT; intuition; eauto.
  - rewrite H; eauto. 
  - inversion H; eauto. 
Qed. *)

Global Instance jsonifiable_string : Jsonifiable StringT :=
  {
    to_JSON := JSON_String;
    from_JSON := (fun v => resultC (JSON_to_stringT v));
    (* canonical_serialization := canonical_serialization_stringT *)
  }.

(* The Pair JSONIFIABLE Class *)
Global Instance jsonifiable_pair (A B : Type) `{Jsonifiable A, Jsonifiable B} : Jsonifiable (A * B) :=
  {
    to_JSON := (fun '(a, b) => JSON_Array (cons (to_JSON a) (cons (to_JSON b) nil)));
    from_JSON := (fun js => 
                    match js with
                    | JSON_Array (cons a (cons b nil)) =>
                        match from_JSON a, from_JSON b with
                        | resultC a', resultC b' => resultC (a', b')
                        | errC e, _ => errC e
                        | _, errC e => errC e
                        end
                    | _ => errC errStr_json_to_pair
                    end)
  }.
(* Lemma canonical_serialization_id_type : forall (js : JSON) (a : ID_Type), 
  JSON_String (ID_Type_to_stringT a) = js <-> (match js with | JSON_String s => stringT_to_ID_Type s | _ => errC errStr_json_to_id_type end = @resultC _ StringT a).
Proof.
  intuition; simpl in *.
  - pose proof (canonical_serialization_stringT js (ID_Type_to_stringT a)); intuition.
    inversion H0.
    rewrite H3.
    pose proof (canonical_string_id_type (ID_Type_to_stringT a) a); intuition.
  - pose proof (canonical_string_id_type (JSON_to_stringT js) a).
    intuition.
    rewrite H0.
    pose proof (canonical_serialization js (JSON_to_stringT js)).
    simpl in *; intuition.
Qed. *)

Global Instance jsonifiable_ID_type : Jsonifiable ID_Type :=
  {
    to_JSON := (fun v => JSON_String (ID_Type_to_stringT v));
    from_JSON := (fun v => 
                    match v with
                    | JSON_String s => stringT_to_ID_Type s
                    | _ => errC errStr_json_to_id_type
                    end);
    (* canonical_serialization := canonical_serialization_id_type *)
  }.

Definition string_map_to_JSON {B : Type} `{Jsonifiable B} (m : MapC StringT B) : JSON :=
  JSON_Object (map_map to_JSON m).

Definition JSON_to_string_map {B : Type} `{Jsonifiable B} (js : JSON) 
    : ResultT (MapC StringT B) StringT :=
  match js with
  | JSON_Object m => 
      result_map 
        (fun '(k, v) => 
            match (from_JSON v) with
            | errC e => errC e
            | resultC v' => resultC (k, v')
            end) m
  | _ => errC errStr_json_to_map
  end.

Global Instance jsonifiable_string_map (A : Type) `{Jsonifiable A} : Jsonifiable (MapC StringT A) :=
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
