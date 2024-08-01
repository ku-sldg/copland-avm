Require Import Term JSON List String  Stringifiable_Class_Admits ID_Type.

Import ListNotations.

Open Scope string_scope.

Definition ASP_PARAMS_to_JSON `{Jsonifiable ASP_ARGS} (t : ASP_PARAMS) : JSON := 
    match t with
    | asp_paramsC asp_id args plc targ_id => 
        JSON_Object [
          ("ASP_ID", InJSON_String (to_string asp_id));
          ("ASP_ARGS", InJSON_Object (to_JSON args));
          ("ASP_PLC", InJSON_String (to_string plc));
          ("ASP_TARG_ID", InJSON_String (to_string targ_id))
        ]
    end.

Definition ASP_PARAMS_from_JSON `{Jsonifiable ASP_ARGS} (js : JSON) : ResultT ASP_PARAMS string :=
    match (JSON_get_string "ASP_ID" js), (JSON_get_Object "ASP_ARGS" js), 
                        (JSON_get_string "ASP_PLC" js), (JSON_get_string "ASP_TARG_ID" js) with
                  | resultC asp_id, resultC args, resultC plc, resultC targ_id => 
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

Definition FWD_to_JSON (t : FWD) : JSON := 
    match t with
    | COMP => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "COMP")]
    | ENCR => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "ENCR")]
    | EXTD n => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "EXTD"); ("EXTD_N", InJSON_String (to_string n))]
    | KILL => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "KILL")]
    | KEEP => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "KEEP")]
    end.

Definition FWD_from_JSON (js : JSON) : ResultT FWD string :=
    match (JSON_get_string "FWD_CONSTRUCTOR" js) with
                  | resultC cons_name =>
                      if (eqb cons_name "COMP") 
                      then resultC COMP
                      else if (eqb cons_name "ENCR") 
                      then resultC ENCR
                      else if (eqb cons_name "KILL") 
                      then resultC KILL
                      else if (eqb cons_name "KEEP") 
                      then resultC KEEP
                      else if (eqb cons_name "EXTD")
                        then match (JSON_get_string "EXTD_N" js) with
                             | resultC n_str => 
                                match (from_string n_str) with
                                | resultC n => resultC (EXTD n)
                                | errC e => errC e
                                end
                             | _ => errC "Parsing EXTD not successful"
                             end
                      else errC "Invalid FWD JSON"
                  | errC e => errC e
                  end.

Global Instance Jsonifiable_FWD : Jsonifiable FWD.
eapply Build_Jsonifiable with 
  (to_JSON := FWD_to_JSON)
  (from_JSON := FWD_from_JSON).
intuition; simpl in *.
unfold FWD_to_JSON; 
unfold FWD_from_JSON;
repeat break_match; simpl in *; try congruence;
repeat find_injection; simpl in *; try congruence;
rewrite canonical_stringification in *; try congruence; try find_injection.
Defined.

Fixpoint Evidence_to_JSON (e : Evidence) : JSON := 
  match e with
  | mt => JSON_Object [("EVIDENCE_CONSTRUCTOR", InJSON_String "mt")]
  | nn n => 
      JSON_Object [
        ("EVIDENCE_CONSTRUCTOR", InJSON_String "nn"); 
        ("N_ID", InJSON_String (to_string n))
      ]
  | uu plc fwd ps e' => 
      JSON_Object [
        ("EVIDENCE_CONSTRUCTOR", InJSON_String "uu");
        ("PLC", InJSON_String (to_string plc));
        ("FWD", InJSON_Object (to_JSON fwd));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("EVIDENCE", InJSON_Object (Evidence_to_JSON e'))
      ]
  | ss e1 e2 =>
      JSON_Object [
        ("EVIDENCE_CONSTRUCTOR", InJSON_String "ss");
        ("EVIDENCE1", InJSON_Object (Evidence_to_JSON e1));
        ("EVIDENCE2", InJSON_Object (Evidence_to_JSON e2))
      ]
  end.

Fixpoint Evidence_from_JSON (js : JSON) : ResultT Evidence string :=
  match (JSON_get_string "EVIDENCE_CONSTRUCTOR" js) with
  | resultC cons_name =>
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
                (_,InJSON_String plc); 
                (_, InJSON_Object fwd); 
                (_, InJSON_Object asp_par); 
                (_, InJSON_Object ev')
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
                (_,InJSON_Object ev1); 
                (_,InJSON_Object ev2)
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

Global Instance Jsonifiable_Evidence `{Jsonifiable ASP_ARGS} `{Jsonifiable FWD} : Jsonifiable Evidence.
eapply Build_Jsonifiable with (to_JSON := Evidence_to_JSON) (from_JSON := Evidence_from_JSON).
unfold Evidence_from_JSON;
unfold Evidence_to_JSON;
unfold ASP_PARAMS_from_JSON;
unfold ASP_PARAMS_to_JSON;
induction a; simpl in *; intuition.
- rewrite canonical_stringification; eauto.
- rewrite IHa.
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