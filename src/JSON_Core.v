Require Import Term JSON List String  Stringifiable_Class_Admits ID_Type Maps.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require Import Lia.

Import ListNotations.

Open Scope string_scope.

Ltac jsonifiable_hammer := 
  repeat break_match; simpl in *; try congruence;
  repeat find_injection; simpl in *; try congruence;
  repeat rewrite canonical_stringification in *; try congruence; try find_injection; try auto;
  repeat rewrite canonical_jsonification in *; try congruence; try find_injection; try auto.

Theorem fold_right_spec : forall {A B : Type} (f : B -> A -> A) (ls : list B) (init : A) P,
  (forall x, P x -> forall y, P (f y x)) ->
  (P init \/ exists x', In x' ls /\ (forall y, P (f x' y))) ->
  P (fold_right f init ls).
Proof.
  intuition.
  - induction ls; eauto.
  - break_exists; intuition;
    induction ls; simpl in *; intuition; eauto.
    subst; eauto.
Defined.

Lemma map_get_impl_in : forall {A B : Type} `{EqClass A} (m : MapC A B) k v,
  map_get m k = Some v ->
  In (k, v) m.
Proof.
  induction m; simpl in *; intuition; try congruence; eauto.
  jsonifiable_hammer; rewrite eqb_eq in *; subst; eauto.
Defined.

Lemma json_get_object_result_always_smaller : forall js s js',
  JSON_get_Object s js = resultC js' ->
  lt (JSON_depth js') (JSON_depth js).
Proof.
  induction js; simpl in *; intuition; 
  jsonifiable_hammer.
  unfold depth_js_map.
  eapply fold_right_spec; intuition; eauto.
  - lia.
  - right; exists (s, js'); simpl in *; split; try lia.
    eapply map_get_impl_in; eauto.
Defined.

Lemma json_all_map_elements_smaller : forall js m s,
  map_get m s = Some js ->
  lt (JSON_depth js) (JSON_depth (JSON_Object m)).
Proof.
  induction m; simpl in *; intuition; try congruence;
  jsonifiable_hammer.
  - rewrite String.eqb_eq in *; subst; lia.
  - eapply IHm in H; lia.
Defined.

Lemma json_all_array_elements_smaller : forall js ls,
  In js ls ->
  lt (JSON_depth js) (JSON_depth (JSON_Array ls)).
Proof.
  induction ls; simpl in *; intuition; try congruence;
  jsonifiable_hammer; subst; try lia.
Defined.

Definition ASP_PARAMS_to_JSON `{Jsonifiable ASP_ARGS} (t : ASP_PARAMS) : JSON := 
    match t with
    | asp_paramsC asp_id args plc targ_id => 
        JSON_Object [
          ("ASP_ID", JSON_String (to_string asp_id));
          ("ASP_ARGS", (to_JSON args));
          ("ASP_PLC", JSON_String (to_string plc));
          ("ASP_TARG_ID", JSON_String (to_string targ_id))
        ]
    end.

Definition ASP_PARAMS_from_JSON `{Jsonifiable ASP_ARGS} (js : JSON) : ResultT ASP_PARAMS string :=
  match (JSON_get_Object "ASP_ID" js), (JSON_get_Object "ASP_ARGS" js), (JSON_get_Object "ASP_PLC" js), (JSON_get_Object "ASP_TARG_ID" js) with
  | resultC (JSON_String asp_id), resultC args, resultC (JSON_String plc), resultC (JSON_String targ_id) => 
      match (from_string asp_id), (from_JSON args), (from_string plc), (from_string targ_id) with
      | resultC asp_id, resultC args, resultC plc, resultC targ_id => resultC (asp_paramsC asp_id args plc targ_id)
      | _, _, _, _ => errC "Parsing ASP_PARAMS not successful"
      end
  | _, _, _, _ => errC "Invalid ASP_PARAMS JSON"
  end.

Global Instance Jsonifiable_ASP_Params `{Jsonifiable ASP_ARGS} : Jsonifiable ASP_PARAMS. 
eapply Build_Jsonifiable with 
  (to_JSON := ASP_PARAMS_to_JSON) 
  (from_JSON := ASP_PARAMS_from_JSON).
unfold ASP_PARAMS_to_JSON; 
unfold ASP_PARAMS_from_JSON;
intuition; simpl in *;
jsonifiable_hammer.
Defined.


Definition type_string_constant : string := "CONSTRUCTOR".
Definition body_string_constant : string := "BODY".

Definition fwd_name_constant : string := "FWD".
Definition comp_name_constant : string := "COMP".
Definition encr_name_constant : string := "ENCR".
Definition extd_name_constant : string := "EXTD".
Definition kill_name_constant : string := "KILL".
Definition keep_name_constant : string := "KEEP".

Definition evidence_name_constant : string := "Evidence".
Definition mt_name_constant : string := "mt".
Definition nn_name_constant : string := "nn".
Definition uu_name_constant : string := "uu".
Definition ss_name_constant : string := "ss".

Definition noArgConstructor_to_JSON (type_name : string) (cons_name : string) : JSON := 
  JSON_Object [((type_name ++ "_" ++ type_string_constant), JSON_String cons_name)]. 

Definition oneArgConstructor_to_JSON (type_name : string) (cons_name : string) (inner:JSON) : JSON := 
    JSON_Object [
      ((type_name ++ "_" ++ type_string_constant), JSON_String cons_name);
      ((type_name ++ "_" ++ body_string_constant), inner)
    ].

Definition multiArgConstructor_to_JSON (type_name : string) (cons_name : string) (ls:list JSON) : JSON := 
    JSON_Object [
      ((type_name ++ "_" ++ type_string_constant), JSON_String cons_name);
      ((type_name ++ "_" ++ body_string_constant), (JSON_Array ls))
    ].

Definition constructor_to_JSON (type_name : string) (cons_name : string) (ls:list JSON) : JSON := 
  match ls with 
  | [] => noArgConstructor_to_JSON type_name cons_name 
  | [v] => oneArgConstructor_to_JSON type_name cons_name v 
  | _ => multiArgConstructor_to_JSON type_name cons_name ls
  end.

Global Instance Jsonifiable_nat : Jsonifiable nat.
eapply Build_Jsonifiable with
  (to_JSON := (fun s => 
                JSON_String (to_string s)
                ))
  (from_JSON := (fun js => 
                  match js with
                  | JSON_String natString => 
                    match (from_string natString) with 
                    | resultC s => resultC s 
                    | errC e => errC ("Error:  cannot interpret nat string in Jsonifiable_nat:  " ++ e)
                    end
                  | _ => errC "Invalid nat JSON (not a JSON String)"
                  end)).
intros.
break_match;
rewrite canonical_stringification in *; 
try congruence.
Defined.

Definition constructor_body_from_JSON_gen (type_name:string) (js:JSON) 
    : list JSON.
  refine ((match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) -> list JSON with
  | resultC (JSON_Array ls) => fun Heq => ls  (* 2+ constructor args case *)
  | resultC jv => fun Heq => [jv]             (* 1 arg case *)
  | errC _ => fun Heq => nil                   (* 0 args case *)
  end) eq_refl).
Defined.

Definition from_JSON_gen {A:Type} (type_name:string) 
  (cmap: (MapC string (JSON -> (ResultT A string)))) 
    : JSON -> ResultT A string := 
  fun js => 
    match (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) -> ResultT A string with
    | resultC (JSON_String cons_name) =>
      match (map_get cmap cons_name) with 
      | Some f => fun Heq => f js
      | None => fun _ => errC ("Invalid " ++ type_name ++ " JSON:  unrecognized constructor name: " ++ cons_name)
      end
    | resultC _ => fun _ => errC ("Invalid " ++ type_name ++ " JSON:  no constructor name string")
    | errC e => fun _ => errC e
    end eq_refl.

Definition FWD_to_JSON (t : FWD) : JSON := 
  match t with
  | COMP =>   constructor_to_JSON fwd_name_constant comp_name_constant []
  | ENCR =>   constructor_to_JSON fwd_name_constant encr_name_constant []
  | EXTD n => constructor_to_JSON fwd_name_constant extd_name_constant [(to_JSON n)]
  | KILL =>   constructor_to_JSON fwd_name_constant kill_name_constant []
  | KEEP =>   constructor_to_JSON fwd_name_constant keep_name_constant []
  end.

Definition constructor_from_JSON {A:Type} (type_name:string) 
  (f:(list JSON) -> ResultT A string) : (JSON -> ResultT A string) := 
(fun js => f (constructor_body_from_JSON_gen type_name js)).

Definition constructor_body_from_JSON_gen_rec {top_js:JSON} (type_name:string) : { ls : list JSON | (forall y : JSON, In y ls -> JSON_depth y < JSON_depth top_js) }.
destruct (JSON_get_Object (type_name ++ "_" ++ body_string_constant) top_js) eqn:?.
- (* no body, must be 0 args *) 
  exists nil; intuition; simpl in *; intuition.
- destruct j. 
  * (* object, so 1 args case *) 
    exists ([JSON_Object m]); simpl in *.
    intuition; subst.
    eapply json_get_object_result_always_smaller; eauto.
  * (* array so multiple args *) 
    exists l; simpl in *; intuition.
    eapply json_get_object_result_always_smaller in Heqr; eauto.
    eapply PeanoNat.Nat.lt_trans; [ | eauto].
    eapply json_all_array_elements_smaller; eauto.
  * (* string so 1 arg *) 
    exists ([JSON_String s]); simpl in *.
    intuition; subst.
    eapply json_get_object_result_always_smaller; eauto.
  * (* boolean so 1 arg *) 
    exists ([JSON_Boolean b]); simpl in *.
    intuition; subst.
    eapply json_get_object_result_always_smaller; eauto.
Defined.

Definition constructor_from_JSON_rec {A:Type} {top_js : JSON} (type_name:string) 
  (f: { ls : list JSON | (forall y : JSON, In y ls -> JSON_depth y < JSON_depth top_js) } -> ResultT A string) : ResultT A string := 
f (@constructor_body_from_JSON_gen_rec top_js type_name).

Definition FWD_from_JSON_map : MapC string (JSON -> (ResultT FWD string)) := 
  [(comp_name_constant, 
    constructor_from_JSON fwd_name_constant (fun _ => resultC COMP));
   (encr_name_constant, 
    constructor_from_JSON fwd_name_constant (fun _ => resultC ENCR));
   (keep_name_constant, 
    constructor_from_JSON fwd_name_constant (fun _ => resultC KEEP));
   (kill_name_constant, 
    constructor_from_JSON fwd_name_constant (fun _ => resultC KILL));
   (extd_name_constant, 
    constructor_from_JSON fwd_name_constant 
      (fun ljs => 
        match ljs with
        | [n_js] => 
          match from_JSON n_js with
          | resultC n => resultC (EXTD n)
          | _ => errC "Invalid JSON args for EXTD"
          end
        | _ => errC "Invalid JSON args for EXTD"
        end))].

Definition FWD_from_JSON (js : JSON) : ResultT FWD string :=
   from_JSON_gen fwd_name_constant FWD_from_JSON_map js.

Theorem from_JSON_gen_constructor_to_JSON_works : forall {A : Type} tname cname ls jsmap (f : JSON -> ResultT A string) v,
  map_get jsmap cname = Some f ->
  f (constructor_to_JSON tname cname ls) = v ->
  from_JSON_gen tname jsmap (constructor_to_JSON tname cname ls) = v.
Proof.
  induction jsmap; simpl in *; intuition; try congruence.
  repeat jsonifiable_hammer.
  - rewrite String.eqb_eq in *; subst; jsonifiable_hammer; 
    unfold constructor_to_JSON, noArgConstructor_to_JSON, 
      oneArgConstructor_to_JSON, multiArgConstructor_to_JSON,
      from_JSON_gen in *; 
    simpl in *; jsonifiable_hammer;
    try rewrite String.eqb_eq in *; subst; jsonifiable_hammer;
    try rewrite String.eqb_neq in *; jsonifiable_hammer.
  - rewrite String.eqb_neq in *; subst; jsonifiable_hammer; 
    unfold constructor_to_JSON, noArgConstructor_to_JSON, 
      oneArgConstructor_to_JSON, multiArgConstructor_to_JSON,
      from_JSON_gen in *; 
    simpl in *; jsonifiable_hammer;
    try rewrite String.eqb_eq in *; subst; jsonifiable_hammer;
    try rewrite String.eqb_neq in *; jsonifiable_hammer.
Qed.

Lemma string_app_helper : forall s1 s2 s3,
  s1 ++ s2 = s1 ++ s3 <->
  s2 = s3.
Proof.
  induction s1; simpl in *; intuition; eauto.
  - invc H; eapply IHs1; eauto.
  - subst; eauto.
Qed.

Theorem constructor_from_JSON_to_JSON_works : forall {A : Type} tname cname ls (f : list JSON -> ResultT A string) v,
  f ls = v ->
  ~ (exists v', ls = [JSON_Array v']) ->
  constructor_from_JSON tname f (constructor_to_JSON tname cname ls) = v.
Proof.
  intuition; unfold constructor_from_JSON, constructor_body_from_JSON_gen, constructor_to_JSON,
    noArgConstructor_to_JSON, oneArgConstructor_to_JSON,
    multiArgConstructor_to_JSON in *.
  destruct ls.
  - (* ls = nil *) 
    repeat rewrite String.eqb_eq in *; subst; jsonifiable_hammer;
    repeat rewrite String.eqb_neq in *; subst; jsonifiable_hammer;
    try rewrite String.eqb_eq in *; unfold type_string_constant,
    body_string_constant in *;
    try rewrite string_app_helper in *; try congruence.
  - destruct ls. 
    * (* ls = [j] *)
      jsonifiable_hammer;
      repeat rewrite String.eqb_eq in *; subst; jsonifiable_hammer;
      repeat rewrite String.eqb_neq in *; subst; jsonifiable_hammer;
      try rewrite String.eqb_eq in *; unfold type_string_constant,
      body_string_constant in *;
      try rewrite string_app_helper in *; try congruence.
      exfalso; eauto.
    * (* ls = [j] *)
      jsonifiable_hammer;
      repeat rewrite String.eqb_eq in *; subst; jsonifiable_hammer;
      repeat rewrite String.eqb_neq in *; subst; jsonifiable_hammer;
      try rewrite String.eqb_eq in *; unfold type_string_constant,
      body_string_constant in *;
      try rewrite string_app_helper in *; try congruence. 
Qed.

Global Instance Jsonifiable_FWD : Jsonifiable FWD.
eapply Build_Jsonifiable with 
  (to_JSON := FWD_to_JSON)
  (from_JSON := FWD_from_JSON).
intuition; simpl in *.

unfold FWD_to_JSON.
unfold FWD_from_JSON.
break_match;
eapply from_JSON_gen_constructor_to_JSON_works;
unfold FWD_from_JSON_map; try reflexivity.
unfold constructor_from_JSON, constructor_to_JSON,
  oneArgConstructor_to_JSON, constructor_body_from_JSON_gen.
jsonifiable_hammer.
Defined.


Fixpoint Evidence_to_JSON `{Jsonifiable FWD, Jsonifiable nat, Jsonifiable ASP_PARAMS} (e : Evidence) : JSON := 
  match e with
  | mt => 
      constructor_to_JSON evidence_name_constant mt_name_constant []
  | nn n => 
      constructor_to_JSON evidence_name_constant nn_name_constant [(to_JSON n)]
  | uu plc fwd ps e' => 
      constructor_to_JSON evidence_name_constant uu_name_constant 
        [(JSON_String plc); (to_JSON fwd);
          (to_JSON ps); Evidence_to_JSON e']
  | ss e1 e2 => 
      constructor_to_JSON evidence_name_constant ss_name_constant 
        [(Evidence_to_JSON e1); (Evidence_to_JSON e2)]
  end.

Definition nn_args_from_json (ls: list JSON) : ResultT Evidence string := 
  match ls with 
  | [(JSON_String n_str)] => 
      match (from_string n_str) with
      | resultC n => resultC (nn n)
      | errC e => errC e
      end
  | [_] => errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong JSON arg type (expected JSON_String)")
  | _ =>   errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong number of JSON args (expected 1)")
  end.

Definition ss_args_from_json {top_js} (recf: forall y : JSON, JSON_depth y < JSON_depth top_js -> ResultT Evidence string) (ls : {ls : list JSON
  | forall y : JSON, In y ls -> JSON_depth y < JSON_depth top_js}) {HLT : exists s', JSON_get_Object s' top_js = resultC (JSON_Array (proj1_sig ls))}: ResultT Evidence string.
  refine ((match (proj1_sig ls) as ls' return (proj1_sig ls) = ls' -> ResultT Evidence string with
  | [ ev1; 
      ev2 ] => 
      fun Heq =>
      match (recf ev1 _), (recf ev2 _) with
      | resultC evres1, resultC evres2 => resultC (ss evres1 evres2)
      | _, _ => errC "other"
      end
  | [_] => fun _ => errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong JSON arg type (expected JSON_String)")
  | _ =>   fun _ => errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong number of JSON args (expected 1)")
  end) eq_refl); subst; simpl in *; eauto;
  break_exists; find_apply_lem_hyp json_get_object_result_always_smaller; 
  eapply PeanoNat.Nat.lt_trans; try eassumption;
  eapply json_all_array_elements_smaller; 
  rewrite Heq; simpl; eauto.
Defined.

Definition uu_args_from_json {top_js} (recf: forall y : JSON, JSON_depth y < JSON_depth top_js -> ResultT Evidence string) (ls : {ls : list JSON
  | forall y : JSON, In y ls -> JSON_depth y < JSON_depth top_js}) {HLT : exists s', JSON_get_Object s' top_js = resultC (JSON_Array (proj1_sig ls))}: ResultT Evidence string.
  refine ((
    match (proj1_sig ls) as ls' return (proj1_sig ls) = ls' -> ResultT Evidence string with 
  | [(JSON_String plc);
      fwd;
      asp_par; 
      ev' ] => 
      fun Heq =>
      match (from_string plc), (from_JSON fwd), (from_JSON asp_par), (recf ev' _) with
      | resultC plcres, resultC fwdres, resultC parres, resultC evres => resultC (uu plcres fwdres parres evres)
      | _, _, _, _ => errC "other"
      end
  | [_] => fun _ => errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong JSON arg type (expected JSON_String)")
  | _ =>  fun _ => errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong number of JSON args (expected 1)")
  end) eq_refl); subst; simpl in *; eauto.
  destruct HLT.
  eapply json_get_object_result_always_smaller in H as H'.
  eapply PeanoNat.Nat.lt_trans; [ | eauto].
  - eapply json_all_array_elements_smaller.
    rewrite Heq; simpl in *; subst; eauto. 
Defined.

Lemma json_depth_order_wf : well_founded (fun x y => lt (JSON_depth x) (JSON_depth y)).
Proof.
  eapply Wf_nat.well_founded_ltof.
Defined.



Definition Evidence_from_JSON `{Jsonifiable FWD, Jsonifiable nat, Jsonifiable ASP_PARAMS} (js : JSON) : ResultT Evidence string.
generalize js.
refine (Fix json_depth_order_wf (fun _ => ResultT Evidence string)
  (
    fun (js : JSON)
      (rec : forall y : JSON,
             lt (JSON_depth y) (JSON_depth js) ->
             ResultT Evidence string) =>
    let type_name := evidence_name_constant in
    match (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name mt_name_constant) 
      then resultC mt
      else if (eqb cons_name nn_name_constant) 
      then 
          match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) -> ResultT Evidence string with
          | resultC n_js => 
              fun _ =>
              match (from_JSON n_js) with
              | resultC n => resultC (nn n)
              | errC e => errC e
              end
          | errC e => fun _ => errC e
          end eq_refl
      else if (eqb cons_name uu_name_constant) 
      then
          match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) = m' -> ResultT Evidence string with
          | resultC (JSON_Array [
                JSON_String plc; fwd; asp_par; ev'
              ]) =>
                fun _ =>
                match (from_string plc), (from_JSON fwd), (from_JSON asp_par), (rec ev' _) with
                | resultC plc, resultC fwd, resultC ps, resultC e =>
                  resultC (uu plc fwd ps e)
                | _, _, _, _ => errC "other"
                end
          | resultC _ =>  fun _ => errC ("JSON Parsing " ++ uu_name_constant ++ " ARGS:  wrong number of JSON args (expected 4)")
          | errC e => fun _ => errC e
          end eq_refl
      else if (eqb cons_name ss_name_constant) 
      then  
          match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) = m' -> ResultT Evidence string with
          | resultC (JSON_Array [ ev1; ev2 ]) =>
              fun _ =>
                match (rec ev1 _), (rec ev2 _) with
                | resultC e1, resultC e2 => resultC (ss e1 e2)
                | _, _ => errC "other"
                end
          | resultC _ =>  fun _ => errC ("JSON Parsing " ++ ss_name_constant ++ " ARGS:  wrong number of JSON args (expected 2)")
          | errC e => fun _ => errC e
          end eq_refl
      else errC "Invalid Evidence JSON constructor name"
    | resultC _ => errC ("Invalid " ++ type_name ++ " JSON:  no constructor name string")
    | errC e => errC e
    end)).
- eapply json_get_object_result_always_smaller in e as E;
  eapply PeanoNat.Nat.lt_trans; [ | eauto];
  eapply json_all_array_elements_smaller; eauto;
  simpl in *; eauto.
- eapply json_get_object_result_always_smaller in e as E;
  eapply PeanoNat.Nat.lt_trans; [ | eauto];
  eapply json_all_array_elements_smaller; eauto;
  simpl in *; eauto.
- eapply json_get_object_result_always_smaller in e as E;
  eapply PeanoNat.Nat.lt_trans; [ | eauto];
  eapply json_all_array_elements_smaller; eauto;
  simpl in *; eauto.
Defined.

(* Definition Evidence_from_JSON_map {top_js} (recf: forall y : JSON, JSON_depth y < JSON_depth top_js -> ResultT Evidence string) {HLT : forall ls, exists s', JSON_get_Object s' top_js = resultC (JSON_Array ls)} : MapC string (JSON -> (ResultT Evidence string)) :=
  [(mt_name_constant, 
    constructor_from_JSON evidence_name_constant (fun _ => resultC mt));
   (nn_name_constant, 
    constructor_from_JSON evidence_name_constant nn_args_from_json);
   (uu_name_constant, 
    fun top_js => @constructor_from_JSON_rec _ top_js evidence_name_constant (
      fun ls => uu_args_from_json recf ls (HLT (proj1_sig ls))));
   (ss_name_constant,
    fun top_js =>
    constructor_from_JSON_rec evidence_name_constant (
      fun ls => ss_args_from_json recf ls (HLT (proj1_sig ls))))].

Definition from_JSON_gen_rec {A:Type} (type_name:string) 
  (cmap: (MapC string (JSON -> (ResultT A string)))) 
    : JSON -> ResultT A string := 
  fun js => 
    match (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) -> ResultT A string with
    | resultC (JSON_String cons_name) =>
      match (map_get cmap cons_name) with 
      | Some f => fun Heq => f js
      | None => fun _ => errC ("Invalid " ++ type_name ++ " JSON:  unrecognized constructor name: " ++ cons_name)
      end
    | resultC _ => fun _ => errC ("Invalid " ++ type_name ++ " JSON:  no constructor name string")
    | errC e => fun _ => errC e
    end eq_refl.


Program Fixpoint Evidence_from_JSON' (js : JSON) {measure (JSON_depth js)} : ResultT Evidence string :=
  from_JSON_gen evidence_name_constant (@Evidence_from_JSON_map js Evidence_from_JSON') js. *)

(*
Definition Evidence_from_JSON' (js : JSON) (m:MapC string (JSON -> (ResultT Evidence string))) : ResultT Evidence string :=
  from_JSON_gen_nonrec evidence_name_constant m js.

Program Fixpoint Evidence_from_JSON (js : JSON) {measure (JSON_depth js)} : ResultT Evidence string :=
  Evidence_from_JSON' js (Evidence_from_JSON_map (fun js' => Evidence_from_JSON js')).
Next Obligation.
Admitted.
*)

Definition uu_ev_ex : Evidence := uu "P0" COMP (asp_paramsC "i" [] "P0" "P0") mt.

Definition ss_ev_ex : Evidence := ss uu_ev_ex uu_ev_ex.

Example uuev_ex : (Evidence_from_JSON (Evidence_to_JSON uu_ev_ex) = (resultC uu_ev_ex)).
Proof.
  intros.
  jsonifiable_hammer.
Qed.

Example ssev_ex : (Evidence_from_JSON (Evidence_to_JSON ss_ev_ex) = (resultC ss_ev_ex)).
Proof.
  intros.
  jsonifiable_hammer.
Qed.

Theorem Evidence_from_JSON_eq : forall `{Jsonifiable FWD, Jsonifiable nat, Jsonifiable ASP_PARAMS} (js : JSON),
  Evidence_from_JSON js = 
    let type_name := evidence_name_constant in
    match (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name mt_name_constant) 
      then resultC mt
      else if (eqb cons_name nn_name_constant) 
      then 
          match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) -> ResultT Evidence string with
          | resultC n_js => 
              fun _ =>
              match (from_JSON n_js) with
              | resultC n => resultC (nn n)
              | errC e => errC e
              end
          | errC e => fun _ => errC e
          end eq_refl
      else if (eqb cons_name uu_name_constant) 
      then
          match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) = m' -> ResultT Evidence string with
          | resultC (JSON_Array [
                JSON_String plc; fwd; asp_par; ev'
              ]) =>
                fun _ =>
                match (from_string plc), (from_JSON fwd), (from_JSON asp_par), (Evidence_from_JSON ev') with
                | resultC plc, resultC fwd, resultC ps, resultC e =>
                  resultC (uu plc fwd ps e)
                | _, _, _, _ => errC "other"
                end
          | resultC _ =>  fun _ => errC ("JSON Parsing " ++ uu_name_constant ++ " ARGS:  wrong number of JSON args (expected 4)")
          | errC e => fun _ => errC e
          end eq_refl
      else if (eqb cons_name ss_name_constant) 
      then  
          match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) = m' -> ResultT Evidence string with
          | resultC (JSON_Array [ ev1; ev2 ]) =>
              fun _ =>
                match (Evidence_from_JSON ev1), (Evidence_from_JSON ev2) with
                | resultC e1, resultC e2 => resultC (ss e1 e2)
                | _, _ => errC "other"
                end
          | resultC _ =>  fun _ => errC ("JSON Parsing " ++ ss_name_constant ++ " ARGS:  wrong number of JSON args (expected 2)")
          | errC e => fun _ => errC e
          end eq_refl
      else errC "Invalid Evidence JSON constructor name"
    | resultC _ => errC ("Invalid " ++ type_name ++ " JSON:  no constructor name string")
    | errC e => errC e
    end.
Proof.
  intros; apply (Fix_eq json_depth_order_wf (fun _ => ResultT Evidence string)); intros; intuition;
  repeat (break_match; eauto; intuition; eauto; try congruence;
    try rewrite String.eqb_eq in *; subst; 
    try rewrite String.eqb_neq in *; subst; try congruence
  ).
  - generalize (eq_refl ((JSON_get_Object (evidence_name_constant ++ "_" ++ body_string_constant) x))).
    intros.
    (* Print case_eq.
  
  set (X := JSON_get_Object (evidence_name_constant ++ "_" ++ body_string_constant) x) in *.
    dependent destruction X.
    * admit.
    * subst. 
      dependent rewrite <- x.
    destruct x; try (simpl in *; congruence).
    destruct m; try (simpl in *; congruence);
    destruct p; try (simpl in *; congruence).
    destruct s; try (simpl in *; congruence);
    destruct j; try (simpl in *; congruence).
    *  
    destruct (JSON_get_Object (evidence_name_constant ++ "_" ++ body_string_constant) x).
  
  unfold JSON_get_Object.
    destruct x.
    * unfold map_get.
    destruct (JSON_get_Object (evidence_name_constant ++ "_" ++ body_string_constant) x).
  
    generalize (evidence_name_constant ++ "_" ++ body_string_constant).
    destruct (JSON_get_Object (evidence_name_constant ++ "_" ++ body_string_constant) x) eqn:?.
    subst.
    * 
    set (M := JSON_get_Object X1 x) in *.
    generalize_eqs M.
    destruct M.
    destruct M.
    destruct (JSON_get_Object X1 x) eqn:?; try congruence;
    destruct j; try congruence; try find_injection. *)

Admitted.

Global Instance Jsonifiable_Evidence `{Jsonifiable ASP_ARGS, Jsonifiable FWD, Jsonifiable nat, Jsonifiable ASP_PARAMS} : Jsonifiable Evidence.
eapply Build_Jsonifiable with (to_JSON := Evidence_to_JSON) (from_JSON := Evidence_from_JSON).
induction a; rewrite Evidence_from_JSON_eq; simpl in *;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *;
jsonifiable_hammer.
Defined.

Global Instance Stringifiable_SP : Stringifiable SP := {
  to_string := (fun sp => 
                  match sp with
                  | ALL => "ALL"
                  | NONE => "NONE"
                  end);
  from_string := (fun s => 
                    if (eqb s "ALL")
                    then resultC ALL
                    else if (eqb s "NONE")
                    then resultC NONE
                    else errC "Invalid SP string");
  canonical_stringification := fun s => match s with
                                        | ALL => eq_refl
                                        | NONE => eq_refl
                                        end
}.

Definition ASP_to_JSON `{Jsonifiable FWD, Stringifiable Plc, Stringifiable SP, Jsonifiable ASP_PARAMS} (t : ASP) : JSON := 
  match t with
  | NULL => constructor_to_JSON "ASP" "NULL" []
  | CPY => constructor_to_JSON "ASP" "CPY" []
  | ASPC sp fwd ps => 
      constructor_to_JSON "ASP" "ASPC" 
        [(JSON_String (to_string sp)); (to_JSON fwd); (to_JSON ps)]
  | SIG => constructor_to_JSON "ASP" "SIG" []
  | HSH => constructor_to_JSON "ASP" "HSH" []
  | ENC q => 
      constructor_to_JSON "ASP" "ENC" 
        [(JSON_String (to_string q))]
  end.


Definition ASP_from_JSON_map `{Jsonifiable FWD, Stringifiable Plc, Stringifiable SP, Jsonifiable ASP_PARAMS}: MapC string (JSON -> (ResultT ASP string)) := 
  [("NULL", constructor_from_JSON "ASP" (fun _ => resultC NULL));
   ("CPY", constructor_from_JSON "ASP" (fun _ => resultC CPY));
   ("ASPC", constructor_from_JSON "ASP" 
      (fun ljs =>
        match ljs with
        | [JSON_String sp_js; fwd_js; ps_js] => 
            match (from_string sp_js), (from_JSON fwd_js), (from_JSON ps_js) with
            | resultC sp, resultC fwd, resultC ps => resultC (ASPC sp fwd ps)
            | _, _, _ => errC "Parsing ASPC not successful"
            end
        | _ => errC "Parsing ASPC not successful"
        end));
   ("SIG", constructor_from_JSON "ASP" (fun _ => resultC SIG));
   ("HSH", constructor_from_JSON "ASP" (fun _ => resultC HSH));
   ("ENC", constructor_from_JSON "ASP" 
      (fun ljs => 
        match ljs with
        | [JSON_String n_js] => 
          match from_string n_js with
          | resultC n => resultC (ENC n)
          | _ => errC "Invalid JSON args for ENC"
          end
        | _ => errC "Invalid JSON args for ENC"
        end))].

Definition ASP_from_JSON `{Jsonifiable FWD, Jsonifiable ASP_PARAMS} (js : JSON) : ResultT ASP string :=
   from_JSON_gen "ASP" ASP_from_JSON_map js.

Global Instance Jsonifiable_ASP `{Jsonifiable FWD, Jsonifiable ASP_PARAMS}: Jsonifiable ASP.
eapply (Build_Jsonifiable) with 
  (to_JSON := ASP_to_JSON)
  (from_JSON := ASP_from_JSON).
unfold ASP_to_JSON, ASP_from_JSON; intros a.
break_match;
eapply from_JSON_gen_constructor_to_JSON_works;
unfold ASP_from_JSON_map; try reflexivity.
unfold constructor_from_JSON, constructor_to_JSON,
  oneArgConstructor_to_JSON, constructor_body_from_JSON_gen.
repeat jsonifiable_hammer.
Defined.

Global Instance Jsonifiable_Split : Jsonifiable Split := {
  to_JSON := (fun '(s1, s2) => 
                JSON_Object [
                  ("split1", JSON_String (to_string s1));
                  ("split2", JSON_String (to_string s2))
                ]);
  from_JSON := (fun js => 
                  match (JSON_get_string "split1" js), (JSON_get_string "split2" js) with
                  | resultC s1, resultC s2 => 
                      match (from_string s1), (from_string s2) with
                      | resultC s1, resultC s2 => resultC (s1, s2) 
                      | _, _ => errC "Parsing split not successful"
                      end
                  | _, _ => errC "Invalid Split JSON"
                  end);
  canonical_jsonification := fun '(s1, s2) => 
                              match s1, s2 with
                              | ALL, ALL => eq_refl
                              | NONE, NONE => eq_refl
                              | _, _ => eq_refl
                              end
}.

Fixpoint Term_to_JSON `{Jsonifiable ASP, Jsonifiable Split} (t : Term) : JSON := 
  match t with
  | asp a => constructor_to_JSON "TERM" "asp" [(to_JSON a)]
  | att p t' => constructor_to_JSON "TERM" "att" 
      [(JSON_String (to_string p)); (Term_to_JSON t')]
  | lseq t1 t2 => constructor_to_JSON "TERM" "lseq"
      [(Term_to_JSON t1); (Term_to_JSON t2)]
  | bseq sp t1 t2 => constructor_to_JSON "TERM" "bseq"
      [(to_JSON sp); (Term_to_JSON t1); (Term_to_JSON t2)]
  | bpar sp t1 t2 => constructor_to_JSON "TERM" "bpar"
      [(to_JSON sp); (Term_to_JSON t1); (Term_to_JSON t2)]
  end.

Import ResultNotation.

Definition Term_from_JSON `{Jsonifiable ASP, Jsonifiable Split} (js : JSON) : ResultT Term string.
generalize js.
refine (Fix json_depth_order_wf (fun _ => ResultT Term string)
  (
    fun (js : JSON)
      (rec : forall y : JSON,
             lt (JSON_depth y) (JSON_depth js) ->
             ResultT Term string) =>
    let type_name := "TERM" in
    let type_str := type_name ++ "_" ++ type_string_constant in
    let body_str := type_name ++ "_" ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name "asp") 
      then 
        asp_js <- (JSON_get_Object body_str js) ;;
        asp_val <- from_JSON asp_js ;;
        resultC (asp asp_val)
      else if (eqb cons_name "att") 
      then 
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [JSON_String plc; term']) =>
            fun _ =>
            plc_val <- from_string plc ;;
            term_val <- (rec term' _) ;;
            resultC (att plc_val term_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'att' ARGS: Incorrect number or wrong type of JSON args (expected [plc; term])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "lseq") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [ term1; term2 ]) =>
            fun _ =>
            term1_val <- (rec term1 _) ;;
            term2_val <- (rec term2 _) ;;
            resultC (lseq term1_val term2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'lseq' ARGS: Incorrect number or wrong type of JSON args (expected [term1; term2])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "bseq") 
      then  
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [ sp; term1; term2 ]) =>
            fun _ =>
            sp_val <- from_JSON sp ;;
            term1_val <- (rec term1 _) ;;
            term2_val <- (rec term2 _) ;;
            resultC (bseq sp_val term1_val term2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'bseq' ARGS: Incorrect number or wrong type of JSON args (expected [sp; term1; term2])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "bpar") 
      then  
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [ sp; term1; term2 ]) =>
            fun _ =>
            sp_val <- from_JSON sp ;;
            term1_val <- (rec term1 _) ;;
            term2_val <- (rec term2 _) ;;
            resultC (bpar sp_val term1_val term2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'bpar' ARGS: Incorrect number or wrong type of JSON args (expected [sp; term1; term2])")
        | errC e => fun _ => errC e
        end eq_refl
      else errC "Invalid Term JSON constructor name"
    | resultC _ => errC "Invalid Term type"
    | errC e => errC e
    end)); eapply json_get_object_result_always_smaller in e as E;
  eapply PeanoNat.Nat.lt_trans; try eassumption;
  eapply json_all_array_elements_smaller; 
  simpl in *; eauto.
Defined.

Theorem Term_from_JSON_eq : forall `{Jsonifiable ASP, Jsonifiable Split} (js : JSON),
  Term_from_JSON js = 
    let type_name := "TERM" in
    let type_str := type_name ++ "_" ++ type_string_constant in
    let body_str := type_name ++ "_" ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name "asp") 
      then 
        asp_js <- (JSON_get_Object body_str js) ;;
        asp_val <- from_JSON asp_js ;;
        resultC (asp asp_val)
      else if (eqb cons_name "att") 
      then 
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [JSON_String plc; term']) =>
            fun _ =>
            plc_val <- from_string plc ;;
            term_val <- (Term_from_JSON term') ;;
            resultC (att plc_val term_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'att' ARGS: Incorrect number or wrong type of JSON args (expected [plc; term])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "lseq") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [ term1; term2 ]) =>
            fun _ =>
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            resultC (lseq term1_val term2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'lseq' ARGS: Incorrect number or wrong type of JSON args (expected [term1; term2])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "bseq") 
      then  
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [ sp; term1; term2 ]) =>
            fun _ =>
            sp_val <- from_JSON sp ;;
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            resultC (bseq sp_val term1_val term2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'bseq' ARGS: Incorrect number or wrong type of JSON args (expected [sp; term1; term2])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "bpar") 
      then  
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT Term string with
        | resultC (JSON_Array [ sp; term1; term2 ]) =>
            fun _ =>
            sp_val <- from_JSON sp ;;
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            resultC (bpar sp_val term1_val term2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'bpar' ARGS: Incorrect number or wrong type of JSON args (expected [sp; term1; term2])")
        | errC e => fun _ => errC e
        end eq_refl
      else errC "Invalid Term JSON constructor name"
    | resultC _ => errC "Invalid Term type"
    | errC e => errC e
    end.
Proof.
  intros; apply (Fix_eq json_depth_order_wf (fun _ => ResultT Term string)); intros; intuition;
  repeat (break_match; eauto; intuition; eauto; try congruence;
    try rewrite String.eqb_eq in *; subst; 
    try rewrite String.eqb_neq in *; subst; try congruence
  ).
  - admit.
  - admit. 
  - admit.
  - admit. 
Admitted. 

Global Instance Jsonifiable_Term `{Jsonifiable ASP, Jsonifiable Split} : Jsonifiable Term. 
eapply Build_Jsonifiable with (to_JSON := Term_to_JSON) (from_JSON := Term_from_JSON).
induction a; rewrite Term_from_JSON_eq; simpl in *;
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *).
Defined.

Global Instance Jsonifiable_RawEv : Jsonifiable RawEv. 
  eapply Build_Jsonifiable with (to_JSON := (fun ev => 
                JSON_Object [
                  ("RawEv", JSON_Array (map (fun bs => JSON_String (to_string bs)) ev))
                ]))
  (from_JSON := (fun js => 
                  match (JSON_get_Array "RawEv" js) with
                  | resultC js' => 
                      result_map (fun js' => 
                                    match js' with
                                    | JSON_String s => 
                                        match (from_string s) with
                                        | resultC bs => resultC bs
                                        | errC e => errC e
                                        end
                                    | _ => errC "Invalid RawEv JSON"
                                    end) js'
                  | errC e => errC e
                  end)).
induction a; simpl in *; intuition; eauto;
repeat rewrite canonical_stringification in *; simpl in *;
find_rewrite; eauto.
Defined.

Fixpoint AppResultC_to_JSON `{Jsonifiable ASP_PARAMS, Jsonifiable Split, Jsonifiable RawEv} (a : AppResultC) : JSON := 
  match a with
  | mtc_app => constructor_to_JSON "AppResultC" "mtc_app" []
  | nnc_app n bs => constructor_to_JSON "AppResultC" "nnc_app"
      [(JSON_String (to_string n)); (JSON_String (to_string bs))]
  | ggc_app plc ps rawev res =>
      constructor_to_JSON "AppResultC" "ggc_app"
      [(JSON_String (to_string plc)); (to_JSON ps);
        (to_JSON rawev); (AppResultC_to_JSON res)]
  | hhc_app plc ps bs res =>
      constructor_to_JSON "AppResultC" "hhc_app"
      [(JSON_String (to_string plc)); (to_JSON ps);
        (JSON_String (to_string bs)); (AppResultC_to_JSON res)]
  | eec_app plc ps bs res =>
      constructor_to_JSON "AppResultC" "eec_app"
      [(JSON_String (to_string plc)); (to_JSON ps);
        (JSON_String (to_string bs)); (AppResultC_to_JSON res)]
  | ssc_app res1 res2 =>
      constructor_to_JSON "AppResultC" "ssc_app"
      [(AppResultC_to_JSON res1); (AppResultC_to_JSON res2)]
  end.

Definition AppResultC_from_JSON `{Jsonifiable ASP_PARAMS, Jsonifiable Split, Jsonifiable RawEv} (js : JSON) : ResultT AppResultC string.
generalize js.
refine (Fix json_depth_order_wf (fun _ => ResultT AppResultC string)
  (
    fun (js : JSON)
      (rec : forall y : JSON,
             lt (JSON_depth y) (JSON_depth js) ->
             ResultT AppResultC string) =>
    let type_name := "AppResultC" in
    let type_str := type_name ++ "_" ++ type_string_constant in
    let body_str := type_name ++ "_" ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name "mtc_app") 
      then resultC (mtc_app)
      else if (eqb cons_name "nnc_app") 
      then 
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [JSON_String n; JSON_String bs]) =>
            fun _ =>
            n_val <- from_string n ;;
            bs_val <- from_string bs ;;
            resultC (nnc_app n_val bs_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'nnc_app' ARGS: Incorrect number or wrong type of JSON args (expected [n; bs])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "ggc_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ JSON_String plc; ps; rawev; res ]) =>
            fun _ =>
            plc_val <- from_string plc ;;
            ps_val <- from_JSON ps ;;
            rawev_val <- from_JSON rawev ;;
            res_val <- (rec res _) ;;
            resultC (ggc_app plc_val ps_val rawev_val res_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'ggc_app' ARGS: Incorrect number or wrong type of JSON args (expected [plc; ps; rawev; res])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "hhc_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ JSON_String plc; ps; JSON_String bs; res ]) =>
            fun _ =>
            plc_val <- from_string plc ;;
            ps_val <- from_JSON ps ;;
            bs_val <- from_string bs ;;
            res_val <- (rec res _) ;;
            resultC (hhc_app plc_val ps_val bs_val res_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'hhc_app' ARGS: Incorrect number or wrong type of JSON args (expected [plc; ps; bs; res])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "eec_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ JSON_String plc; ps; JSON_String bs; res ]) =>
            fun _ =>
            plc_val <- from_string plc ;;
            ps_val <- from_JSON ps ;;
            bs_val <- from_string bs ;;
            res_val <- (rec res _) ;;
            resultC (eec_app plc_val ps_val bs_val res_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'eec_app' ARGS: Incorrect number or wrong type of JSON args (expected [plc; ps; bs; res])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "ssc_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ res1 ; res2 ]) =>
            fun _ =>
            res1_val <- (rec res1 _) ;;
            res2_val <- (rec res2 _) ;;
            resultC (ssc_app res1_val res2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'ssc_app' ARGS: Incorrect number or wrong type of JSON args (expected [ res1 ; res2 ])")
        | errC e => fun _ => errC e
        end eq_refl
      else errC "Invalid AppResultC JSON constructor name"
    | resultC _ => errC "Invalid AppResultC type"
    | errC e => errC e
    end)); eapply json_get_object_result_always_smaller in e as E;
  eapply PeanoNat.Nat.lt_trans; try eassumption;
  eapply json_all_array_elements_smaller; 
  simpl in *; eauto.
Defined.

Theorem AppResultC_from_JSON_eq : forall `{Jsonifiable ASP_PARAMS, Jsonifiable Split, Jsonifiable RawEv} (js : JSON),
  AppResultC_from_JSON js = 
    let type_name := "AppResultC" in
    let type_str := type_name ++ "_" ++ type_string_constant in
    let body_str := type_name ++ "_" ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name "mtc_app") 
      then resultC (mtc_app)
      else if (eqb cons_name "nnc_app") 
      then 
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [JSON_String n; JSON_String bs]) =>
            fun _ =>
            n_val <- from_string n ;;
            bs_val <- from_string bs ;;
            resultC (nnc_app n_val bs_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'nnc_app' ARGS: Incorrect number or wrong type of JSON args (expected [n; bs])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "ggc_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ JSON_String plc; ps; rawev; res ]) =>
            fun _ =>
            plc_val <- from_string plc ;;
            ps_val <- from_JSON ps ;;
            rawev_val <- from_JSON rawev ;;
            res_val <- (AppResultC_from_JSON res) ;;
            resultC (ggc_app plc_val ps_val rawev_val res_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'ggc_app' ARGS: Incorrect number or wrong type of JSON args (expected [plc; ps; rawev; res])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "hhc_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ JSON_String plc; ps; JSON_String bs; res ]) =>
            fun _ =>
            plc_val <- from_string plc ;;
            ps_val <- from_JSON ps ;;
            bs_val <- from_string bs ;;
            res_val <- (AppResultC_from_JSON res) ;;
            resultC (hhc_app plc_val ps_val bs_val res_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'hhc_app' ARGS: Incorrect number or wrong type of JSON args (expected [plc; ps; bs; res])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "eec_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ JSON_String plc; ps; JSON_String bs; res ]) =>
            fun _ =>
            plc_val <- from_string plc ;;
            ps_val <- from_JSON ps ;;
            bs_val <- from_string bs ;;
            res_val <- (AppResultC_from_JSON res) ;;
            resultC (eec_app plc_val ps_val bs_val res_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'eec_app' ARGS: Incorrect number or wrong type of JSON args (expected [plc; ps; bs; res])")
        | errC e => fun _ => errC e
        end eq_refl
      else if (eqb cons_name "ssc_app") 
      then
        match (JSON_get_Object body_str js) as m' return (JSON_get_Object body_str js) = m' -> ResultT AppResultC string with
        | resultC (JSON_Array [ res1 ; res2 ]) =>
            fun _ =>
            res1_val <- (AppResultC_from_JSON res1) ;;
            res2_val <- (AppResultC_from_JSON res2) ;;
            resultC (ssc_app res1_val res2_val)
        | resultC _ => fun _ => errC ("JSON Parsing 'ssc_app' ARGS: Incorrect number or wrong type of JSON args (expected [ res1 ; res2 ])")
        | errC e => fun _ => errC e
        end eq_refl
      else errC "Invalid AppResultC JSON constructor name"
    | resultC _ => errC "Invalid AppResultC type"
    | errC e => errC e
    end.
Proof.
  intros; apply (Fix_eq json_depth_order_wf (fun _ => ResultT AppResultC string)); intros; intuition;
  repeat (break_match; eauto; intuition; eauto; try congruence;
    try rewrite String.eqb_eq in *; subst; 
    try rewrite String.eqb_neq in *; subst; try congruence
  ); admit.
Admitted. 

Global Instance Jsonifiable_AppResultC `{Jsonifiable ASP_PARAMS, Jsonifiable Split, Jsonifiable RawEv} : Jsonifiable AppResultC.
eapply Build_Jsonifiable with (to_JSON := AppResultC_to_JSON) (from_JSON := AppResultC_from_JSON).
induction a; rewrite AppResultC_from_JSON_eq; simpl in *;
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *).
Defined.

Close Scope string_scope.