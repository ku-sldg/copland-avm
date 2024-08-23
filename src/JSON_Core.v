Require Import Term JSON List String Stringifiable_Class_Admits ID_Type Maps
Interface_Strings_Vars.

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

Definition type_string_constant : string := "CONSTRUCTOR".
Definition body_string_constant : string := "BODY".

Definition fwd_name_constant  : string := "FWD".
Definition comp_name_constant : string := "COMP".
Definition encr_name_constant : string := "ENCR".
Definition extd_name_constant : string := "EXTD".
Definition kill_name_constant : string := "KILL".
Definition keep_name_constant : string := "KEEP".

Definition mt_name_constant : string := "mt_evt".
Definition nonce_evt_name_constant : string := "nonce_evt".
Definition asp_evt_name_constant : string := "asp_evt".
Definition split_evt_name_constant : string := "split_evt".

Definition asp_name_constant  : string := "asp".
Definition null_name_constant : string := "NULL".
Definition appr_name_constant : string := "APPR".
Definition copy_name_constant : string := "CPY".
Definition aspc_name_constant : string := "ASPC".
Definition sig_name_constant  : string := "SIG".
Definition hsh_name_constant  : string := "HSH".
Definition enc_name_constant  : string := "ENC".

Definition evidencet_name_constant : string := "EvidenceT".

Definition att_name_constant  : string := "att".
Definition lseq_name_constant : string := "lseq".
Definition bseq_name_constant : string := "bseq".
Definition bpar_name_constant : string := "bpar".

Definition rawev_name_constant : string := "RawEv".

Definition sp_name_constant   : string := "SP".
Definition all_name_constant  : string := "ALL".
Definition none_name_constant : string := "NONE".


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
jsonifiable_hammer.
Defined.

Definition constructor_body_from_JSON_gen (type_name:string) (js:JSON) 
    : list JSON :=
  match (JSON_get_Object (type_name ++ "_" ++ body_string_constant) js) with
  | resultC (JSON_Array ls) => ls  (* 2+ constructor args case *)
  | resultC jv => [jv]             (* 1 arg case *)
  | errC _ => nil                   (* 0 args case *)
  end.

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
          | _ => errC ("Invalid JSON args for " ++ extd_name_constant)
          end
        | _ => errC ("Invalid JSON args for " ++ extd_name_constant)
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


Fixpoint EvidenceT_to_JSON `{Jsonifiable FWD, Jsonifiable nat, Jsonifiable ASP_PARAMS} (e : EvidenceT) : JSON := 
  match e with
  | mt_evt=> constructor_to_JSON evidencet_name_constant mt_name_constant []
  | nonce_evt n => 
      constructor_to_JSON evidencet_name_constant nonce_evt_name_constant 
        [(to_JSON n)]
  | asp_evt plc ps e' => 
      constructor_to_JSON evidencet_name_constant asp_evt_name_constant 
        [(JSON_String plc); (to_JSON ps); EvidenceT_to_JSON e']
  | split_evt e1 e2 => 
      constructor_to_JSON evidencet_name_constant split_evt_name_constant 
        [(EvidenceT_to_JSON e1); (EvidenceT_to_JSON e2)]
  end.

Fixpoint EvidenceT_from_JSON `{Jsonifiable FWD, Jsonifiable nat, Jsonifiable ASP_PARAMS} (js : JSON) : ResultT EvidenceT string :=
    let type_name := evidencet_name_constant in
    match (JSON_get_Object (type_name ++ "_" ++ type_string_constant) js) with
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
          | _ => errC ("JSON Parsing " ++ nonce_evt_name_constant ++ " ARGS:  wrong number of JSON args (expected 1)")
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
          | _ => errC ("JSON Parsing " ++ asp_evt_name_constant ++ " ARGS:  wrong number of JSON args (expected 3)")
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
          | _ => errC ("JSON Parsing " ++ split_evt_name_constant ++ " ARGS:  wrong number of JSON args (expected 2)")
          end 
      else errC "Invalid EvidenceT JSON constructor name"
    | resultC _ => errC ("Invalid " ++ type_name ++ " JSON:  no constructor name string")
    | errC e => errC e
    end.

Global Instance Jsonifiable_EvidenceT `{Jsonifiable ASP_ARGS, Jsonifiable FWD, Jsonifiable nat, Jsonifiable ASP_PARAMS} : Jsonifiable EvidenceT.
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
                    else errC ("Invalid " ++ sp_name_constant ++ " string"));
  canonical_stringification := fun s => match s with
                                        | ALL => eq_refl
                                        | NONE => eq_refl
                                        end
}.

Definition ASP_to_JSON `{Jsonifiable FWD, Stringifiable Plc, Stringifiable SP, Jsonifiable ASP_PARAMS} (t : ASP) : JSON := 
  match t with
  | NULL => constructor_to_JSON STR_ASP null_name_constant []
  | CPY => constructor_to_JSON STR_ASP copy_name_constant []
  | APPR => constructor_to_JSON STR_ASP appr_name_constant []
  | ASPC sp ps => 
      constructor_to_JSON STR_ASP aspc_name_constant 
        [(JSON_String (to_string sp)); (to_JSON ps)]
  | SIG => constructor_to_JSON STR_ASP sig_name_constant []
  | HSH => constructor_to_JSON STR_ASP hsh_name_constant []
  | ENC q => 
      constructor_to_JSON STR_ASP enc_name_constant 
        [(JSON_String (to_string q))]
  end.


Definition ASP_from_JSON_map `{Jsonifiable FWD, Stringifiable Plc, Stringifiable SP, Jsonifiable ASP_PARAMS}: MapC string (JSON -> (ResultT ASP string)) := 
  [(null_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC NULL));
   (copy_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC CPY));
   (appr_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC APPR));
   (aspc_name_constant, constructor_from_JSON STR_ASP 
      (fun ljs =>
        match ljs with
        | [JSON_String sp_js; ps_js] => 
            match (from_string sp_js), (from_JSON ps_js) with
            | resultC sp, resultC ps => resultC (ASPC sp ps)
            | _, _ => errC ("Parsing " ++ aspc_name_constant ++ " not successful")
            end
        | _ => errC ("Parsing " ++ aspc_name_constant ++ " not successful")
        end));
   (sig_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC SIG));
   (hsh_name_constant, constructor_from_JSON STR_ASP (fun _ => resultC HSH));
   (enc_name_constant, constructor_from_JSON STR_ASP 
      (fun ljs => 
        match ljs with
        | [JSON_String n_js] => 
          match from_string n_js with
          | resultC n => resultC (ENC n)
          | _ => errC ("Invalid JSON args for " ++ enc_name_constant)
          end
        | _ => errC ("Invalid JSON args for " ++ enc_name_constant)
        end))].

Definition ASP_from_JSON `{Jsonifiable FWD, Jsonifiable ASP_PARAMS} (js : JSON) : ResultT ASP string :=
   from_JSON_gen STR_ASP ASP_from_JSON_map js.

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
    let type_str := type_name ++ "_" ++ type_string_constant in
    let body_str := type_name ++ "_" ++ body_string_constant in
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
        | _ => errC ("JSON Parsing " ++ "'" ++ att_name_constant ++ "' ARGS: Incorrect number or wrong type of JSON args (expected [plc; term])")
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
        | _ => errC ("JSON Parsing " ++ "'" ++ lseq_name_constant ++ "' ARGS: Incorrect number or wrong type of JSON args (expected [term1; term2])")
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
        | _ => errC ("JSON Parsing " ++ "'" ++ bseq_name_constant ++ "' ARGS: Incorrect number or wrong type of JSON args (expected [sp; term1; term2])")
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
        | _ => errC ("JSON Parsing " ++ "'" ++ bpar_name_constant ++ "' ARGS: Incorrect number or wrong type of JSON args (expected [sp; term1; term2])")
        end
      else errC ("Invalid " ++ STR_TERM ++ " JSON constructor name")
    | resultC _ => errC ("Invalid " ++ STR_TERM ++ " JSON type")
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
                                    | _ => errC ("Invalid " ++ rawev_name_constant ++ " JSON")
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
      | _ => errC "Invalid Evidence JSON"
      end)
  ); 
destruct a; solve_json.
Defined.

Global Instance Jsonifiable_GlobalContext `{Stringifiable ASP_ID, Jsonifiable FWD,
  Jsonifiable (MapC ASP_ID ASP_ID), Jsonifiable (MapC ASP_ID FWD)} : Jsonifiable GlobalContext. 
eapply Build_Jsonifiable with 
  (to_JSON := (fun g => 
                JSON_Object [
                  ("ASP_Types", to_JSON (asp_types g));
                  ("ASP_Comps", to_JSON (asp_comps g))
                ]))
  (from_JSON := (fun j =>
    match (JSON_get_Object "ASP_Types" j), (JSON_get_Object "ASP_Comps" j) with
    | resultC ats, resultC acs => 
      match (from_JSON ats), (from_JSON acs) with
      | resultC ats, resultC acs => resultC {| asp_types := ats; asp_comps := acs |}
      | _, _ => errC "Error in parsing GlobalContext"
      end
    | _, _ => errC "Error in parsing GlobalContext"
    end)); solve_json.
Defined.

Close Scope string_scope.