Require Import Term JSON List String  Stringifiable_Class_Admits ID_Type Maps.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require Import Lia.

Import ListNotations.

Open Scope string_scope.

Ltac jsonifiable_hammer := 
  repeat break_match; simpl in *; try congruence;
  repeat find_injection; simpl in *; try congruence;
  try rewrite canonical_stringification in *; try congruence; try find_injection; try auto.

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
Qed.

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
Qed.

Lemma json_all_map_elements_smaller : forall js m s,
  map_get m s = Some js ->
  lt (JSON_depth js) (JSON_depth (JSON_Object m)).
Proof.
  induction m; simpl in *; intuition; try congruence;
  jsonifiable_hammer.
  - rewrite String.eqb_eq in *; subst; lia.
  - eapply IHm in H; lia.
Qed.

Lemma json_all_array_elements_smaller : forall js ls,
  In js ls ->
  lt (JSON_depth js) (JSON_depth (JSON_Array ls)).
Proof.
  induction ls; simpl in *; intuition; try congruence;
  jsonifiable_hammer; subst; try lia.
Qed.



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
repeat break_match; simpl in *; try congruence;
repeat find_injection;
try rewrite canonical_jsonification in *; try congruence; try find_injection.
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


Fixpoint Evidence_to_JSON (e : Evidence) : JSON := 
  match e with
  | mt => 
      constructor_to_JSON evidence_name_constant mt_name_constant []
  | nn n => 
      constructor_to_JSON evidence_name_constant nn_name_constant [(to_JSON n)]
  | uu plc fwd ps e' => 
      constructor_to_JSON evidence_name_constant uu_name_constant 
        [(JSON_String plc);
          (to_JSON fwd);
          (to_JSON ps);
          Evidence_to_JSON e']
  | ss e1 e2 => 
      constructor_to_JSON evidence_name_constant ss_name_constant 
        [(Evidence_to_JSON e1);
          (Evidence_to_JSON e2)]
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

Definition Evidence_from_JSON_map {top_js} (recf: forall y : JSON, JSON_depth y < JSON_depth top_js -> ResultT Evidence string) {HLT : forall ls, exists s', JSON_get_Object s' top_js = resultC (JSON_Array ls)} : MapC string (JSON -> (ResultT Evidence string)) :=
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

Lemma json_depth_order_wf : well_founded (fun x y => lt (JSON_depth x) (JSON_depth y)).
Proof.
  eapply Wf_nat.well_founded_ltof.
Defined.

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
  from_JSON_gen evidence_name_constant (@Evidence_from_JSON_map js Evidence_from_JSON') js.

Definition Evidence_from_JSON (js : JSON) : ResultT Evidence string.
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
          | resultC (JSON_Array [(JSON_String n_str)]) => 
              fun _ =>
              match (from_string n_str) with
              | resultC n => resultC (nn n)
              | errC e => errC e
              end
          | resultC _ =>  fun _ => errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong number of JSON args (expected 1)")
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


(*

Fixpoint Evidence_from_JSON (js : JSON) : ResultT Evidence string :=
  match (JSON_get_Object "EVIDENCE_CONSTRUCTOR" js) with
  | resultC (JSON_String cons_name) =>
      if (eqb cons_name "mt") 
      then resultC mt
      else if (eqb cons_name "nn") 
      then  match (JSON_get_string "N_ID" js) with
            | resultC nVal => 
              match (from_string nVal) with
              | resultC n => resultC (nn n)
              | errC e => errC e
              end
            | _ => errC "Parsing nn not successful"
            end
      else if (eqb cons_name "uu") 
      then  match js with
            | JSON_Object [
                ev_cons; 
                (_, JSON_String plc); 
                (_, fwd); 
                (_, asp_par); 
                (_, ev')
              ] =>
                match (from_string plc), (from_JSON fwd), (from_JSON asp_par), (Evidence_from_JSON ev') with
                | resultC plc, resultC fwd, resultC ps, resultC e =>
                  resultC (uu plc fwd ps e)
                | _, _, _, _ => errC "Evidence_from_JSON: error parsing uu"
                end
            | _ => errC "Parsing uu not successful"
            end
      else if (eqb cons_name "ss") 
      then  match js with
            | JSON_Object [
                ev_cons; 
                (_, ev1); 
                (_, ev2)
              ] =>
                match (Evidence_from_JSON ev1), (Evidence_from_JSON ev2) with
                | resultC e1, resultC e2 => resultC (ss e1 e2)
                | _, _ => errC "Parsing ss not successful"
                end
            | _ => errC "Parsing ss not successful"
            end
      else errC "Invalid Evidence JSON constructor name"
  | errC e => errC e
  end.
*)
Theorem Evidence_from_JSON_eq : forall js,
  Evidence_from_JSON js = 
    let type_name := evidence_name_constant in
    match (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name mt_name_constant) 
      then resultC mt
      else if (eqb cons_name nn_name_constant) 
      then 
          match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) -> ResultT Evidence string with
          | resultC (JSON_Array [(JSON_String n_str)]) => 
              fun _ =>
              match (from_string n_str) with
              | resultC n => resultC (nn n)
              | errC e => errC e
              end
          | resultC _ =>  fun _ => errC ("JSON Parsing " ++ nn_name_constant ++ " ARGS:  wrong number of JSON args (expected 1)")
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
  intros; apply (Fix_eq json_depth_order_wf (fun _ => ResultT Evidence string)); intros; intuition; repeat (jsonifiable_hammer;
  try match goal with
    | [ |- context [ match ?X as _ return _ with _ => _ end ] ] =>
      destruct X eqn:?
  end;
    try rewrite String.eqb_eq in *; subst; 
    try rewrite String.eqb_neq in *; subst; try congruence;
    eauto).
  - destruct x; simpl in *; intuition.
    jsonifiable_hammer.
    set (x := json_get_object_result_always_smaller _ _ _).
    repeat jsonifiable_hammer.
    destruct (JSON_get_Object (String (Ascii.Ascii true false true false false false true false) (String (Ascii.Ascii false true true false true true true false) (String (Ascii.Ascii true false false true false true true false) (String (Ascii.Ascii false false true false false true true false) (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii false true true true false true true false) (String (Ascii.Ascii true true false false false true true false) (String (Ascii.Ascii true false true false false true true false) (String (Ascii.Ascii true true true true true false true false) body_string_constant))))))))) x).
    destruct x; simpl in *.
  match goal with
    | [ |- context [ match ?X as _ return _ with _ => _ end ] ] =>
      destruct X eqn:?
  end.
  - jsonifiable_hammer. 

  try match goal with
    | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
  end; simpl; f_equal; auto.
Qed.
  
  if le_lt_dec 2 (length ls)
    then let lss := split ls in
      merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
    else ls.

Global Instance Jsonifiable_Evidence `{Jsonifiable ASP_ARGS} `{Jsonifiable FWD} : Jsonifiable Evidence.
eapply Build_Jsonifiable with (to_JSON := Evidence_to_JSON) (from_JSON := Evidence_from_JSON).
unfold Evidence_from_JSON;
unfold Evidence_to_JSON;
unfold ASP_PARAMS_from_JSON;
unfold ASP_PARAMS_to_JSON.
induction a; simpl in *; intuition; jsonifiable_hammer.
eapply Fix_eq.
Search Fix.
-
  cbn.
  jsonifiable_hammer.
- cbn.
  jsonifiable_hammer.
  unfold from_JSON_gen in *.
  repeat jsonifiable_hammer.
  rewrite IHa.
  clear IHa.
  destruct f; simpl in *;
  try rewrite canonical_stringification; eauto;
  cbv;
  destruct a; simpl in *; intuition;
  induction a1; simpl in *; intuition; eauto; 
  repeat break_match; simpl in *; intuition;
  try rewrite canonical_stringification in *; eauto;
  repeat find_injection; try congruence.
- rewrite IHa1, IHa2; eauto. 
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

Definition ASP_to_JSON (t : ASP) : JSON := 
  match t with
  | NULL => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "NULL")]
  | CPY => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "CPY")]
  | ASPC sp fwd ps => 
      JSON_Object [
        ("ASP_CONSTRUCTOR", InJSON_String "ASPC");
        ("ASP_SP", InJSON_String (to_string sp));
        ("ASP_FWD", InJSON_Object (to_JSON fwd));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps))
      ]
  | SIG => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "SIG")]
  | HSH => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "HSH")]
  | ENC q => 
      JSON_Object [
        ("ASP_CONSTRUCTOR", InJSON_String "ENC");
        ("ENC_PLC", InJSON_String (to_string q))
      ]
  end.

Definition ASP_from_JSON (js : JSON) : ResultT ASP string :=
  match (JSON_get_string "ASP_CONSTRUCTOR" js) with
  | resultC cons_name =>
      if (eqb cons_name "NULL")
      then resultC NULL
      else if (eqb cons_name "CPY")
      then resultC CPY
      else if (eqb cons_name "ASPC")
      then match (JSON_get_string "ASP_SP" js), (JSON_get_Object "ASP_FWD" js), (JSON_get_Object "ASP_PARAMS" js) with
           | resultC sp, resultC fwd, resultC ps =>
              match (from_string sp), (from_JSON fwd), (from_JSON ps) with
              | resultC sp, resultC fwd, resultC ps => 
                  resultC (ASPC sp fwd ps)
              | _, _, _ => errC "Parsing ASPC not successful"
              end
           | _, _, _ => errC "Parsing ASPC not successful"
           end
      else if (eqb cons_name "SIG")
      then resultC SIG
      else if (eqb cons_name "HSH")
      then resultC HSH
      else if (eqb cons_name "ENC")
      then match (JSON_get_string "ENC_PLC" js) with
           | resultC q => 
              match (from_string q) with
              | resultC q => resultC (ENC q)
              | _ => errC "Parsing ENC PLC from string not successful"
              end
           | _ => errC "Parsing ENC not successful"
           end
      else errC "Invalid JSON ASP Constructor Name"
  | _ => errC "Invalid JSON ASP Constructor Name"
  end.

Global Instance Jsonifiable_ASP : Jsonifiable ASP.
eapply (Build_Jsonifiable) with 
  (to_JSON := ASP_to_JSON)
  (from_JSON := ASP_from_JSON).
(* intuition.
repeat (try break_match; subst; simpl in *; intuition; repeat find_injection; try congruence);
try rewrite canonical_stringification in *; eauto; try congruence;
match goal with
| A : ASP_ARGS |- _ => induction A; simpl in *; intuition; eauto;
                        repeat break_match; simpl in *; intuition; eauto;
                        repeat find_injection; try congruence;
                        try rewrite canonical_stringification in *; eauto; try congruence

end.
- simpl in *.  *)

unfold ASP_to_JSON in *;
unfold ASP_from_JSON in *.

destruct a; simpl in *; intuition.
destruct a;
destruct s; simpl in *; intuition;
unfold FWD_to_JSON in *; 
unfold FWD_from_JSON in *;
destruct f; simpl in *; intuition;
unfold ASP_PARAMS_to_JSON in *;
unfold ASP_PARAMS_from_JSON in *;
destruct a; simpl in *; intuition;
induction a0; simpl in *; intuition; eauto;

repeat break_match; simpl in *; intuition;
repeat find_injection; try congruence;
try rewrite canonical_stringification in *; eauto; try congruence.
Qed.

Global Instance Jsonifiable_Split : Jsonifiable Split := {
  to_JSON := (fun '(s1, s2) => 
                JSON_Object [
                  ("split1", InJSON_String (to_string s1));
                  ("split2", InJSON_String (to_string s2))
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


(* NOTE: Very lame on Coq's part, we have to do a list
encoding of the TERM_BODY because it cannot understand
how the recursive calls are truly on subterms otherwise *)
Fixpoint Term_to_JSON (t : Term) : JSON :=
  match t with
  | asp a => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "asp"); 
      ("TERM_BODY", InJSON_Object (to_JSON a))
    ]
  | att p t1 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "att");
      ("TERM_BODY", InJSON_Array [
          (InJSON_String (to_string p)); 
          (InJSON_Object (Term_to_JSON t1))
        ]
      )
    ]
  | lseq t1 t2 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "lseq");
      ("TERM_BODY", InJSON_Array [
          (InJSON_Object (Term_to_JSON t1));
          (InJSON_Object (Term_to_JSON t2))
        ]
      )
    ]
  | bseq s t1 t2 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "bseq");
      ("TERM_BODY", InJSON_Array [
          (InJSON_Object (to_JSON s));
          (InJSON_Object (Term_to_JSON t1));
          (InJSON_Object (Term_to_JSON t2))
        ]
      )
    ]
  | bpar s t1 t2 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "bpar");
      ("TERM_BODY", InJSON_Array [
          (InJSON_Object (to_JSON s));
          (InJSON_Object (Term_to_JSON t1));
          (InJSON_Object (Term_to_JSON t2))
        ]
      )
    ]
  end.

Fixpoint Term_from_JSON (js : JSON) : ResultT Term string :=
  match (JSON_get_string "TERM_CONSTRUCTOR" js) with
  | resultC cons_name =>
      if (eqb cons_name "asp")
      then  match (JSON_get_Object "TERM_BODY" js) with
            | resultC js' => 
                match (from_JSON js') with
                | resultC a => resultC (asp a)
                | errC e => errC e
                end
            | errC e => errC e
            end
      else if (eqb cons_name "att")
      then (*! I hate this, but only viable way without going wf recursion *)
          match js with
          | JSON_Object [
              term_cons; 
              (_, InJSON_Array [InJSON_String plc; InJSON_Object js'])
            ] =>
              match (from_string plc), (Term_from_JSON js') with
              | resultC plc, resultC t => resultC (att plc t)
              | _, _ => errC "Parsing att not successful"
              end
          | _ => errC "Invalid att JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
          end
      else if (eqb cons_name "lseq")
      then  match js with
            | JSON_Object [
                term_cons; 
                (_, InJSON_Array [InJSON_Object t1js; InJSON_Object t2js])
              ] =>
                match (Term_from_JSON t1js), (Term_from_JSON t2js) with
                | resultC t1, resultC t2 => resultC (lseq t1 t2)
                | _, _ => errC "Parsing lseq not successful"
                end
            | _ => errC "Invalid lseq JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
            end
      else if (eqb cons_name "bseq")
      then  match js with
            | JSON_Object [
                term_cons; 
                (_, InJSON_Array [InJSON_Object spjs; InJSON_Object t1js; InJSON_Object t2js])
              ] =>
                match (from_JSON spjs), (Term_from_JSON t1js), (Term_from_JSON t2js) with
                | resultC s, resultC t1, resultC t2 => resultC (bseq s t1 t2)
                | _, _, _ => errC "Parsing bseq not successful"
                end
            | _ => errC "Invalid bseq JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
            end
      else if (eqb cons_name "bpar")
      then  match js with
            | JSON_Object [
                term_cons; 
                (_, InJSON_Array [InJSON_Object spjs; InJSON_Object t1js; InJSON_Object t2js])
              ] =>
                match (from_JSON spjs), (Term_from_JSON t1js), (Term_from_JSON t2js) with
                | resultC s, resultC t1, resultC t2 => resultC (bpar s t1 t2)
                | _, _, _ => errC "Parsing bpar not successful"
                end
            | _ => errC "Invalid bpar JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
            end
      else errC "Invalid TERM CONSTRUCTOR in Term_from_JSON"
  | errC e => errC e
  end.

Global Instance Jsonifiable_Term `{Jsonifiable ASP} : Jsonifiable Term. 
eapply Build_Jsonifiable with (to_JSON := Term_to_JSON) (from_JSON := Term_from_JSON).
induction a; simpl in *; intuition; eauto;
repeat (
  match goal with
  | a : Split |- _ => destruct a
  | a : ASP |- _ => destruct a
  | a : FWD |- _ => destruct a
  | a : ASP_PARAMS |- _ => destruct a
  | a : SP |- _ => destruct a
  | a : ASP_ARGS |- _ => 
      induction a; simpl in *; intuition; eauto;
      simpl in *;
      repeat (break_match; simpl in *; try congruence);
      repeat find_injection; eauto;
      rewrite canonical_stringification in *; try congruence
  end; simpl in *; intuition; eauto);
  try (rewrite canonical_jsonification in *; congruence);
repeat find_rewrite; eauto.
Defined.

Global Instance Jsonifiable_RawEv : Jsonifiable RawEv. 
  eapply Build_Jsonifiable with (to_JSON := (fun ev => 
                JSON_Object [
                  ("RawEv", InJSON_Array (map (fun bs => InJSON_String (to_string bs)) ev))
                ]))
  (from_JSON := (fun js => 
                  match (JSON_get_Array "RawEv" js) with
                  | resultC js' => 
                      result_map (fun js' => 
                                    match js' with
                                    | InJSON_String s => 
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

Fixpoint AppResultC_to_Json `{Jsonifiable ASP_ARGS, Jsonifiable RawEv} (a : AppResultC) : JSON :=
  match a with
  | mtc_app => JSON_Object [("AppResultC_CONSTRUCTOR", InJSON_String "mtc_app")]
  | nnc_app n bs => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "nnc_app");
        ("N_ID", InJSON_String (to_string n));
        ("BS", InJSON_String (to_string bs))
      ]
  | ggc_app plc ps rawEv res => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "ggc_app");
        ("PLC", InJSON_String (to_string plc));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("RawEv", InJSON_Object (to_JSON rawEv));
        ("AppResultC", InJSON_Object (AppResultC_to_Json res))
      ]
  | hhc_app plc ps bs res => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "hhc_app");
        ("PLC", InJSON_String (to_string plc));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("BS", InJSON_String (to_string bs));
        ("AppResultC", InJSON_Object (AppResultC_to_Json res))
      ]
  | eec_app plc ps bs res => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "eec_app");
        ("PLC", InJSON_String (to_string plc));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("BS", InJSON_String (to_string bs));
        ("AppResultC", InJSON_Object (AppResultC_to_Json res))
      ]
  | ssc_app res1 res2 => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "ssc_app");
        ("AppResultC1", InJSON_Object (AppResultC_to_Json res1));
        ("AppResultC2", InJSON_Object (AppResultC_to_Json res2))
      ]
  end.

Fixpoint AppResultC_from_JSON `{Jsonifiable ASP_ARGS, Jsonifiable RawEv} (js : JSON) : ResultT AppResultC string :=
  match (JSON_get_string "AppResultC_CONSTRUCTOR" js) with
  | resultC cons_name =>
      if (eqb cons_name "mtc_app")
      then resultC mtc_app
      else if (eqb cons_name "nnc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String n);
                (_, InJSON_String bs)
              ] => 
                match (from_string n), (from_string bs) with
                | resultC n, resultC bs => resultC (nnc_app n bs)
                | _, _ => errC "Parsing nnc_app not successful"
                end
            | _ => errC "Parsing nnc_app not successful"
            end
      else if (eqb cons_name "ggc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String plc);
                (_, InJSON_Object ps);
                (_, InJSON_Object rawEv);
                (_, InJSON_Object res)
              ] =>
                match (from_string plc), (from_JSON ps), (from_JSON rawEv), (AppResultC_from_JSON res) with
                | resultC plc, resultC ps, resultC rawEv, resultC res => resultC (ggc_app plc ps rawEv res)
                | _, _, _, _ => errC "Parsing ggc_app not successful"
                end
            | _ => errC "Parsing ggc_app not successful"
            end
      else if (eqb cons_name "hhc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String plc);
                (_, InJSON_Object ps);
                (_, InJSON_String bs);
                (_, InJSON_Object res)
              ] =>
                  match (from_string plc), (from_JSON ps), (from_string bs), (AppResultC_from_JSON res) with
                  | resultC plc, resultC ps, resultC bs, resultC res => resultC (hhc_app plc ps bs res)
                  | _, _, _, _ => errC "Parsing hhc_app not successful"
                  end
            | _ => errC "Parsing hhc_app not successful"
            end
      else if (eqb cons_name "eec_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String plc);
                (_, InJSON_Object ps);
                (_, InJSON_String bs);
                (_, InJSON_Object res)
              ] =>
                match (from_string plc), (from_JSON ps), (from_string bs), (AppResultC_from_JSON res) with
                | resultC plc, resultC ps, resultC bs, resultC res => resultC (eec_app plc ps bs res)
                | _, _, _, _ => errC "Parsing eec_app not successful"
                end
            | _ => errC "Parsing eec_app not successful"
            end
      else if (eqb cons_name "ssc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_Object res1);
                (_, InJSON_Object res2)
              ] =>
                match (AppResultC_from_JSON res1), (AppResultC_from_JSON res2) with
                | resultC res1, resultC res2 => resultC (ssc_app res1 res2)
                | _, _ => errC "Parsing ssc_app not successful"
                end
            | _ => errC "Parsing ssc_app not successful"
            end
      else errC "Invalid AppResultC JSON"
  | _ => errC "Invalid AppResultC JSON: No Constructor"
  end.

Global Instance Jsonifiable_AppResultC `{Jsonifiable ASP_ARGS} : Jsonifiable AppResultC.
eapply Build_Jsonifiable with (to_JSON := AppResultC_to_Json) (from_JSON := AppResultC_from_JSON).
induction a; simpl in *; intuition; eauto;
repeat find_rewrite; eauto;
repeat rewrite canonical_stringification in *; eauto;
clear IHa;
repeat (
  match goal with
  | a : Split |- _ => destruct a
  | a : ASP |- _ => destruct a
  | a : FWD |- _ => destruct a
  | a : ASP_PARAMS |- _ => destruct a
  | a : SP |- _ => destruct a
  | a : RawEv |- _ => 
      induction a; simpl in *; intuition; eauto;
      simpl in *;
      repeat (break_match; simpl in *; try congruence);
      repeat find_injection; eauto;
      repeat rewrite canonical_stringification in *; eauto; try congruence;
      repeat rewrite canonical_jsonification in *; eauto; try congruence
  | a : ASP_ARGS |- _ => 
      induction a; simpl in *; intuition; eauto;
      simpl in *;
      repeat (break_match; simpl in *; try congruence);
      repeat find_injection; eauto;
      rewrite canonical_stringification in *; try congruence
  end; simpl in *; intuition; eauto;
  repeat rewrite canonical_jsonification; eauto).


  unfold ASP_PARAMS_from_JSON in *.
  
  simpl in *; intuition; eauto;
  repeat rewrite canonical_jsonification; eauto.
  simpl in *;
  repeat (break_match; simpl in *; try congruence);
  repeat find_injection; eauto;
  try rewrite canonical_stringification in *; try congruence;
  simpl in *; intuition; eauto.
  rewrite canonical_jsonification in *; try congruence.

  unfold ASP_PARAMS_from_JSON in *.
  
  simpl in *; intuition; eauto;
  repeat rewrite canonical_jsonification; eauto.
  simpl in *;
  repeat (break_match; simpl in *; try congruence);
  repeat find_injection; eauto;
  try rewrite canonical_stringification in *; try congruence;
  simpl in *; intuition; eauto.
  rewrite canonical_jsonification in *; try congruence.

  unfold ASP_PARAMS_from_JSON in *.
  
  simpl in *; intuition; eauto;
  repeat rewrite canonical_jsonification; eauto.

  unfold ASP_PARAMS_from_JSON in *.
  
  simpl in *; intuition; eauto;
  repeat rewrite canonical_jsonification; eauto.
Defined.

Close Scope string_scope.