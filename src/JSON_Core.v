Require Import Term_Defs_Core JSON List String Stringifiable_Class_Admits ID_Type Maps
Interface_Strings_Vars ErrorStringConstants.
Require Export JSON_Core_Strings.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require Import Lia.

Import ListNotations.
Import ResultNotation.

Open Scope string_scope.

Ltac jsonifiable_hammer := 
  intros;
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

Lemma map_get_impl_in : forall {A B : Type} `{EqClass A} (m : Map A B) k v,
  map_get k m = Some v ->
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
  map_get s m = Some js ->
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
          (STR_ASP_ID, JSON_String (to_string asp_id));
          (STR_ASP_ARGS, (to_JSON args));
          (STR_ASP_PLC, JSON_String (to_string plc));
          (STR_ASP_TARG_ID, JSON_String (to_string targ_id))
        ]
    end.

Definition ASP_PARAMS_from_JSON `{Jsonifiable ASP_ARGS} (js : JSON) : ResultT ASP_PARAMS string :=
  asp_id  <- JSON_get_string STR_ASP_ID js ;;
  args    <- JSON_get_Object STR_ASP_ARGS js ;;
  plc     <- JSON_get_string STR_ASP_PLC js ;;
  targ    <- JSON_get_string STR_ASP_TARG_ID js ;;

  asp_id' <- from_string asp_id ;;
  args'   <- from_JSON args ;;
  plc'    <- from_string plc ;;
  targ'   <- from_string targ ;;
  resultC (asp_paramsC asp_id' args' plc' targ').

Global Instance Jsonifiable_ASP_Params `{Jsonifiable ASP_ARGS} : Jsonifiable ASP_PARAMS. 
eapply Build_Jsonifiable with 
  (to_JSON := ASP_PARAMS_to_JSON) 
  (from_JSON := ASP_PARAMS_from_JSON).
unfold ASP_PARAMS_to_JSON; 
unfold ASP_PARAMS_from_JSON;
intuition; simpl in *;
jsonifiable_hammer.
Defined.


Definition noArgConstructor_to_JSON (type_name : string) (cons_name : string) : JSON := 
  JSON_Object [((type_name ++ type_sep ++ type_string_constant), JSON_String cons_name)]. 

Definition oneArgConstructor_to_JSON (type_name : string) (cons_name : string) (inner:JSON) : JSON := 
    JSON_Object [
      ((type_name ++ type_sep ++ type_string_constant), JSON_String cons_name);
      ((type_name ++ type_sep ++ body_string_constant), inner)
    ].

Definition multiArgConstructor_to_JSON (type_name : string) (cons_name : string) (ls:list JSON) : JSON := 
    JSON_Object [
      ((type_name ++ type_sep ++ type_string_constant), JSON_String cons_name);
      ((type_name ++ type_sep ++ body_string_constant), (JSON_Array ls))
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
                    | errC e => errC err_str_json_cannot_interp_nat
                    end
                  | _ => errC err_str_json_nat_string
                  end)).
jsonifiable_hammer.
Defined.

Definition constructor_body_from_JSON_gen (type_name:string) (js:JSON) 
    : list JSON :=
  match (JSON_get_Object (type_name ++ type_sep ++ body_string_constant) js) with
  | resultC (JSON_Array ls) => ls  (* 2+ constructor args case *)
  | resultC jv => [jv]             (* 1 arg case *)
  | errC _ => nil                   (* 0 args case *)
  end.

Definition from_JSON_gen {A:Type} (type_name:string) 
  (cmap: (Map string (JSON -> (ResultT A string)))) 
    : JSON -> ResultT A string := 
  fun js => 
    match (JSON_get_Object (type_name ++ type_sep ++ type_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ type_sep ++ type_string_constant) js) -> ResultT A string with
    | resultC (JSON_String cons_name) =>
      match (map_get cons_name cmap) with 
      | Some f => fun Heq => f js
      | None => fun _ => errC err_str_json_unrecognized_constructor
      end
    | resultC _ => fun _ => errC err_str_json_no_constructor_name_string
    | errC e => fun _ => errC e
    end eq_refl.

Definition FWD_to_string (t : FWD) : string := 
  match t with
  | REPLACE => replace_name_constant
  | WRAP    => wrap_name_constant
  | UNWRAP  => unwrap_name_constant
  | EXTEND  => extend_name_constant
  end.

Definition constructor_from_JSON {A:Type} (type_name:string) 
  (f:(list JSON) -> ResultT A string) : (JSON -> ResultT A string) := 
(fun js => f (constructor_body_from_JSON_gen type_name js)).

Definition constructor_body_from_JSON_gen_rec {top_js:JSON} (type_name:string) : { ls : list JSON | (forall y : JSON, In y ls -> JSON_depth y < JSON_depth top_js) }.
destruct (JSON_get_Object (type_name ++ type_sep ++ body_string_constant) top_js) eqn:?.
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

Definition FWD_from_string (s : string) : ResultT FWD string :=
  if (eqb s replace_name_constant)
  then resultC REPLACE
  else if (eqb s wrap_name_constant)
  then resultC WRAP
  else if (eqb s unwrap_name_constant)
  then resultC UNWRAP
  else if (eqb s extend_name_constant)
  then resultC EXTEND
  else errC err_str_fwd_from_string.

Theorem from_JSON_gen_constructor_to_JSON_works : forall {A : Type} tname cname ls jsmap (f : JSON -> ResultT A string) v,
  map_get cname jsmap = Some f ->
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
      try rewrite string_app_helper in *; try congruence;
      exfalso; eauto.
    * (* ls = [j] *)
      jsonifiable_hammer;
      repeat rewrite String.eqb_eq in *; subst; jsonifiable_hammer;
      repeat rewrite String.eqb_neq in *; subst; jsonifiable_hammer;
      try rewrite String.eqb_eq in *; unfold type_string_constant,
      body_string_constant in *;
      try rewrite string_app_helper in *; try congruence. 
Qed.

Global Instance Stringifiable_FWD : Stringifiable FWD.
eapply Build_Stringifiable with 
  (to_string := FWD_to_string)
  (from_string := FWD_from_string).
intuition; simpl in *;
unfold FWD_to_string, FWD_from_string; ff.
Defined.

Definition EvOutSig_to_JSON `{Jsonifiable nat} (t : EvOutSig) : JSON := 
  let type_const := ev_out_sig_name_constant ++ type_sep ++ type_string_constant in
  let body_const := ev_out_sig_name_constant ++ type_sep ++ body_string_constant in
  match t with
  | OutN n => JSON_Object 
    [ (type_const, JSON_String outn_name_constant); 
      (body_const, to_JSON n)]
  | OutUnwrap => JSON_Object 
    [(type_const, JSON_String outunwrap_name_constant)]
  end.

Definition EvOutSig_from_JSON `{Jsonifiable nat} (js : JSON) : ResultT EvOutSig string :=
  let type_const := ev_out_sig_name_constant ++ type_sep ++ type_string_constant in
  let body_const := ev_out_sig_name_constant ++ type_sep ++ body_string_constant in
  match (JSON_get_Object type_const js) with
  | resultC (JSON_String cons_name) =>
    if (eqb cons_name outunwrap_name_constant) 
    then resultC OutUnwrap
    else if (eqb cons_name outn_name_constant) 
    then match js with
        | JSON_Object [
            _;
            (_, n_js)
          ] =>
            n_js <- from_JSON n_js ;;
            resultC (OutN n_js)
        | _ => errC err_str_json_parsing_outn
        end
    else errC err_str_evoutsig_json_constructor
  | resultC _ => errC err_str_json_no_constructor_name_string
  | errC e => errC e
  end.

Global Instance Jsonifiable_EvOutSig `{Jsonifiable nat} : Jsonifiable EvOutSig.
eapply Build_Jsonifiable with 
  (to_JSON := EvOutSig_to_JSON)
  (from_JSON := EvOutSig_from_JSON).
unfold EvOutSig_from_JSON, EvOutSig_to_JSON; 
induction a; jsonifiable_hammer.
Defined.

Definition EvSig_to_JSON `{Jsonifiable EvOutSig, Stringifiable FWD} (t : EvSig) : JSON := 
  let '(ev_arrow fwd in_sig out_sig) := t in
  JSON_Object [
    (fwd_name_constant, JSON_String (to_string fwd));
    (ev_in_sig_name_constant, 
      JSON_String (match in_sig with
      | InAll => all_name_constant
      | InNone => none_name_constant
      end));
    (ev_out_sig_name_constant, to_JSON out_sig)].

Definition EvSig_from_JSON `{Jsonifiable EvOutSig, Stringifiable FWD} (js : JSON) : ResultT EvSig string :=
  fwd_js <- JSON_get_string fwd_name_constant js ;;
  in_sig_js <- JSON_get_string ev_in_sig_name_constant js ;;
  out_sig_js <- JSON_get_Object ev_out_sig_name_constant js ;;

  fwd <- from_string fwd_js ;;
  in_sig <- 
    (if (eqb in_sig_js all_name_constant) 
    then resultC InAll
    else if (eqb in_sig_js none_name_constant) 
    then resultC InNone
    else errC err_str_invalid_evinsig_json) ;;
  out_sig <- from_JSON out_sig_js ;;

  resultC (ev_arrow fwd in_sig out_sig).

Global Instance Jsonifiable_EvSig `{Jsonifiable EvOutSig, Stringifiable FWD} : Jsonifiable EvSig.
eapply Build_Jsonifiable with
(to_JSON := EvSig_to_JSON)
(from_JSON := EvSig_from_JSON);
unfold EvSig_from_JSON, EvSig_to_JSON;
destruct a; jsonifiable_hammer; subst; result_monad_unfold; 
jsonifiable_hammer.
Defined.

Fixpoint EvidenceT_to_JSON `{Jsonifiable nat, Jsonifiable ASP_PARAMS} (e : EvidenceT) : JSON := 
  match e with
  | mt_evt=> constructor_to_JSON evidencet_name_constant mt_name_constant []
  | nonce_evt n => 
      constructor_to_JSON evidencet_name_constant nonce_evt_name_constant 
        [(to_JSON n)]
  | asp_evt plc ps e' => 
      constructor_to_JSON evidencet_name_constant asp_evt_name_constant 
        [(JSON_String plc); (to_JSON ps); EvidenceT_to_JSON e']
  | left_evt e' => 
      constructor_to_JSON evidencet_name_constant left_evt_name_constant
        [(EvidenceT_to_JSON e')]
  | right_evt e' => 
      constructor_to_JSON evidencet_name_constant right_evt_name_constant
        [(EvidenceT_to_JSON e')]
  | split_evt e1 e2 => 
      constructor_to_JSON evidencet_name_constant split_evt_name_constant 
        [(EvidenceT_to_JSON e1); (EvidenceT_to_JSON e2)]
  end.

Fixpoint EvidenceT_from_JSON `{Jsonifiable nat, Jsonifiable ASP_PARAMS} (js : JSON) : ResultT EvidenceT string :=
    let type_name := evidencet_name_constant in
    match (JSON_get_Object (type_name ++ type_sep ++ type_string_constant) js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name mt_name_constant) 
      then resultC mt_evt
      else if (eqb cons_name nonce_evt_name_constant) 
      then match js with
          | JSON_Object [
              _;
              (_, n_js)
            ] =>
              n_js <- from_JSON n_js ;;
              resultC (nonce_evt n_js)
          | _ => errC err_str_json_parsing_failure_wrong_number_args
          end
      else if (eqb cons_name asp_evt_name_constant) 
      then match js with
          | JSON_Object [
              _;
              (_, JSON_Array [ JSON_String plc; asp_par; ev' ])
            ] =>
              plc <- from_string plc ;;
              asp_par <- from_JSON asp_par ;;
              ev' <- EvidenceT_from_JSON ev' ;;
              resultC (asp_evt plc asp_par ev')
          | _ => errC err_str_json_parsing_failure_wrong_number_args
          end 
      else if (eqb cons_name left_evt_name_constant)
      then match js with
          | JSON_Object [
              _;
              (_, ev')
           ] =>
              ev' <- EvidenceT_from_JSON ev' ;;
              resultC (left_evt ev')
          | _ => errC err_str_json_parsing_failure_wrong_number_args
          end 
      else if (eqb cons_name right_evt_name_constant)
      then match js with
          | JSON_Object [
              _;
              (_, ev')
           ] =>
              ev' <- EvidenceT_from_JSON ev' ;;
              resultC (right_evt ev')
          | _ => errC err_str_json_parsing_failure_wrong_number_args
          end 
      else if (eqb cons_name split_evt_name_constant) 
      then match js with
          | JSON_Object [
              _;
              (_, JSON_Array [ ev1; ev2 ])
           ] =>
              ev1 <- EvidenceT_from_JSON ev1 ;;
              ev2 <- EvidenceT_from_JSON ev2 ;;
              resultC (split_evt ev1 ev2)
          | _ => errC err_str_json_parsing_failure_wrong_number_args
          end 
      else errC err_str_json_invalid_constructor_name
    | resultC _ => errC err_str_json_no_constructor_name_string
    | errC e => errC e
    end.

Global Instance Jsonifiable_EvidenceT `{Jsonifiable ASP_ARGS, Jsonifiable nat, Jsonifiable ASP_PARAMS} : Jsonifiable EvidenceT.
eapply Build_Jsonifiable with (to_JSON := EvidenceT_to_JSON) (from_JSON := EvidenceT_from_JSON).
induction a; simpl in *;
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *).
Defined.

Global Instance Stringifiable_SP : Stringifiable SP := {
  to_string := (fun sp => 
                  match sp with
                  | ALL => all_name_constant
                  | NONE => none_name_constant
                  end);
  from_string := (fun s => 
                    if (eqb s all_name_constant)
                    then resultC ALL
                    else if (eqb s none_name_constant)
                    then resultC NONE
                    else errC err_str_json_parsing_SP);
  canonical_stringification := fun s => match s with
                                        | ALL => eq_refl
                                        | NONE => eq_refl
                                        end
}.

Definition ASP_to_JSON `{Stringifiable Plc, Jsonifiable ASP_ARGS} (t : ASP) : JSON := 
  match t with
  | NULL => constructor_to_JSON STR_ASP null_name_constant []
  (* | CPY => constructor_to_JSON STR_ASP copy_name_constant [] *)
  | APPR => constructor_to_JSON STR_ASP appr_name_constant []
  | ASPC ps => 
      constructor_to_JSON STR_ASP aspc_name_constant 
        [(to_JSON ps)]
  | SIG => constructor_to_JSON STR_ASP sig_name_constant []
  | HSH => constructor_to_JSON STR_ASP hsh_name_constant []
  | ENC q => 
      constructor_to_JSON STR_ASP enc_name_constant 
        [(JSON_String (to_string q))]
  end.


Definition ASP_from_JSON_map `{Stringifiable Plc, Jsonifiable ASP_ARGS}: Map string (JSON -> (ResultT ASP string)) := 
  [(null_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC NULL));
   (* (copy_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC CPY)); *)
   (appr_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC APPR));
   (aspc_name_constant, constructor_from_JSON STR_ASP 
      (fun ljs =>
        match ljs with
        | [ps_js] => 
            ps <- from_JSON ps_js ;;
            resultC (ASPC ps)
        | _ => errC err_str_json_parsing_ASPC
        end));
   (sig_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC SIG));
   (hsh_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC HSH));
   (enc_name_constant, constructor_from_JSON STR_ASP 
      (fun ljs => 
        match ljs with
        | [JSON_String n_js] => 
          n <- from_string n_js ;;
          resultC (ENC n)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end))].

Definition ASP_from_JSON `{Jsonifiable ASP_ARGS} (js : JSON) : ResultT ASP string :=
   from_JSON_gen STR_ASP ASP_from_JSON_map js.

Global Instance Jsonifiable_ASP `{Jsonifiable ASP_ARGS}: Jsonifiable ASP.
eapply (Build_Jsonifiable) with 
  (to_JSON := ASP_to_JSON)
  (from_JSON := ASP_from_JSON).
induction a; try (ff; fail).
unfold ASP_from_JSON, ASP_to_JSON, from_JSON_gen; ff.
induction a; unfold constructor_from_JSON, constructor_body_from_JSON_gen; 
result_monad_unfold; ff;
unfold ASP_PARAMS_from_JSON in *; ff; result_monad_unfold;
jsonifiable_hammer.
Defined.

Global Instance Jsonifiable_Split : Jsonifiable Split := {
  to_JSON := (fun '(s1, s2) => 
                JSON_Object [
                  (split1_name_constant, JSON_String (to_string s1));
                  (split2_name_constant, JSON_String (to_string s2))
                ]);
  from_JSON := (fun js => 
                  match (JSON_get_string split1_name_constant js), (JSON_get_string split2_name_constant js) with
                  | resultC s1, resultC s2 => 
                    s1 <- from_string s1 ;;
                    s2 <- from_string s2 ;;
                    resultC (s1, s2)
                  | _, _ => errC err_str_json_parsing_failure_wrong_number_args
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
  | asp a => constructor_to_JSON STR_TERM asp_name_constant [(to_JSON a)]
  | att p t' => constructor_to_JSON STR_TERM att_name_constant 
      [(JSON_String (to_string p)); (Term_to_JSON t')]
  | lseq t1 t2 => constructor_to_JSON STR_TERM lseq_name_constant
      [(Term_to_JSON t1); (Term_to_JSON t2)]
  | bseq sp t1 t2 => constructor_to_JSON STR_TERM bseq_name_constant
      [(to_JSON sp); (Term_to_JSON t1); (Term_to_JSON t2)]
  | bpar sp t1 t2 => constructor_to_JSON STR_TERM bpar_name_constant
      [(to_JSON sp); (Term_to_JSON t1); (Term_to_JSON t2)]
  end.

Fixpoint Term_from_JSON `{Jsonifiable ASP, Jsonifiable Split} (js : JSON) : ResultT Term string :=
    let type_name := STR_TERM in
    let type_str := type_name ++ type_sep ++ type_string_constant in
    let body_str := type_name ++ type_sep ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>
      if (eqb cons_name asp_name_constant) 
      then 
        asp_js <- (JSON_get_Object body_str js) ;;
        asp_val <- from_JSON asp_js ;;
        resultC (asp asp_val)
      else if (eqb cons_name att_name_constant) 
      then match js with
        | (JSON_Object [
            _;
            (_, JSON_Array [JSON_String plc; term'])
          ]) =>
            plc_val <- from_string plc ;;
            term_val <- (Term_from_JSON term') ;;
            resultC (att plc_val term_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end
      else if (eqb cons_name lseq_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
         ] =>
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            resultC (lseq term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end
      else if (eqb cons_name bseq_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ sp; term1; term2 ])
          ] =>
            sp_val <- from_JSON sp ;;
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            resultC (bseq sp_val term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end
      else if (eqb cons_name bpar_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ sp; term1; term2 ])
         ] =>
            sp_val <- from_JSON sp ;;
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            resultC (bpar sp_val term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end
      else errC err_str_json_invalid_constructor_name
    | resultC _ => errC err_str_json_invalid_constructor_name
    | errC e => errC e
    end.

Global Instance Jsonifiable_Term `{Jsonifiable ASP, Jsonifiable Split} : Jsonifiable Term. 
eapply Build_Jsonifiable with (to_JSON := Term_to_JSON) (from_JSON := Term_from_JSON).
induction a; 
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *; eauto).
Defined.

Global Instance Jsonifiable_RawEv : Jsonifiable RawEv. 
  eapply Build_Jsonifiable with (to_JSON := (fun ev => 
                JSON_Object [
                  (rawev_name_constant, JSON_Array (map (fun bs => JSON_String (to_string bs)) ev))
                ]))
  (from_JSON := (fun js => 
                  match (JSON_get_Array rawev_name_constant js) with
                  | resultC js' => 
                      result_map (fun js' => 
                                    match js' with
                                    | JSON_String s => 
                                        match (from_string s) with
                                        | resultC bs => resultC bs
                                        | errC e => errC e
                                        end
                                    | _ => errC err_str_json_invalid_constructor_name
                                    end) js'
                  | errC e => errC e
                  end)).
induction a; simpl in *; intuition; eauto;
repeat rewrite canonical_stringification in *; simpl in *;
find_rewrite; eauto.
Defined.

Global Instance Jsonifiable_Evidence `{Jsonifiable RawEv, Jsonifiable EvidenceT}: Jsonifiable Evidence.
eapply Build_Jsonifiable with
  (to_JSON := 
    (fun e => let '(evc r et) := e in
      JSON_Array [ (to_JSON r); (to_JSON et) ])
  )
  (from_JSON := 
    (fun j => 
      match j with
      | JSON_Array [ r_js; et_js ] =>
          r <- from_JSON r_js ;;
          et <- from_JSON et_js ;;
          resultC (evc r et)
      | _ => errC err_str_invalid_evidence_json
      end)
  ); 
destruct a; solve_json.
Defined.

Global Instance Jsonifiable_GlobalContext `{Stringifiable ASP_ID, 
  Jsonifiable (Map ASP_ID ASP_ID), Jsonifiable ASP_Type_Env} : Jsonifiable GlobalContext. 
eapply Build_Jsonifiable with 
  (to_JSON := (fun g => 
                JSON_Object [
                  (asp_types_name_constant, to_JSON (asp_types g));
                  (asp_comps_name_constant, to_JSON (asp_comps g))
                ]))
  (from_JSON := (fun j =>
    ats <- (JSON_get_Object asp_types_name_constant j) ;;
    acs <- (JSON_get_Object asp_comps_name_constant j) ;;
    ats <- from_JSON ats ;;
    acs <- from_JSON acs ;;
    resultC {| asp_types := ats; asp_comps := acs |}
    )); solve_json.
Defined.

Close Scope string_scope.