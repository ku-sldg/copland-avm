Require Import Term_Defs Maps ID_Type EqClass.

Require Import Manifest_Set JSON JSON_Core.

Require Import Flexible_Mechanisms_Vars.

Require Import CACL.

Require Import List.
Import ListNotations.


Open Scope string_scope.

(* CDS demo vars *)

(* Plc IDs *)
Definition cds_config_dir_plc : Plc := "cds_config_dir_plc".

(* TARG IDs *)
Definition kim_evidence_targ : TARG_ID := "kim_evidence_targ".

Definition in_targ  : TARG_ID := "in_targ".
Definition out_targ : TARG_ID := "out_targ".

Definition cds_exe_dir_targ : TARG_ID := "cds_exe_dir_targ".
Definition cds_exe_1_targ : TARG_ID := "cds_exe_1_targ".
Definition cds_exe_2_targ : TARG_ID := "cds_exe_2_targ".
Definition cds_exe_3_targ : TARG_ID := "cds_exe_3_targ".
Definition tmp_1_targ : TARG_ID := "tmp_1_targ".
Definition tmp_2_targ : TARG_ID := "tmp_2_targ".
Definition tmp_3_targ : TARG_ID := "tmp_3_targ".

Definition cds_flags_dir_targ : TARG_ID := "cds_flags_dir_targ".
Definition cds_flags_1_targ : TARG_ID := "cds_flags_1_targ".
Definition cds_flags_2_targ : TARG_ID := "cds_flags_2_targ".
Definition cds_flags_3_targ : TARG_ID := "cds_flags_3_targ".

Definition cds_controller_dir_targ : TARG_ID := "cds_controller_dir_targ".
Definition cds_controller_exe_targ : TARG_ID := "cds_controller_exe_targ".

Definition cds_config_1_targ : TARG_ID := "cds_config_1_targ".
Definition cds_config_2_targ : TARG_ID := "cds_config_2_targ".
Definition cds_config_3_targ : TARG_ID := "cds_config_3_targ".
Definition cds_img_1_targ : TARG_ID := "cds_img_1_targ".
Definition cds_img_2_targ : TARG_ID := "cds_img_2_targ".
Definition cds_img_3_targ : TARG_ID := "cds_img_3_targ".



(* ASP IDs *)
Definition query_kim_id : ASP_ID := "query_kim_id".
Definition hash_file_contents_id : ASP_ID := "hash_file_contents_id".
Definition gather_file_contents_id : ASP_ID := "gather_file_contents_id".
Definition appr_cds_id : ASP_ID := "appr_cds_id".

Close Scope string_scope.




Definition gather_targ_asp (targPlc:Plc) (targId:TARG_ID) : Term := 
    (asp (ASPC (* ALL (EXTD 1)  *)
               (asp_paramsC 
                    gather_file_contents_id 
                    [] 
                    targPlc 
                    targId ))).

Definition hash_targ_asp (targPlc:Plc) (targId:TARG_ID) : Term := 
    (asp (ASPC (* ALL (EXTD 1) *)
                (asp_paramsC 
                    hash_file_contents_id 
                    [] 
                    targPlc 
                    targId ))).


Open Scope cop_ent_scope.

Definition gather_config_1 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_1_targ).

Definition gather_config_2 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_2_targ).

Definition gather_config_3 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_3_targ).

Definition hash_cds_img_1 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_1_targ).

Definition hash_cds_img_2 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_2_targ).

Definition hash_cds_img_3 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_3_targ).

Definition hash_controller_img : Term := 
    (hash_targ_asp cds_controller_dir_targ cds_controller_exe_targ).

Definition meas_cds_phrase : Term :=
<{
    gather_config_1
    (* +<+ *)
    ->
    gather_config_2
    ->
    gather_config_3
    ->
    hash_controller_img 
    ->
    hash_cds_img_1
    ->
    hash_cds_img_2
    ->
    hash_cds_img_3
}>.

Definition query_kim_asp : Term := 
    (asp (ASPC (* ALL (EXTD 1) *) (asp_paramsC query_kim_id [] P1 kim_evidence_targ))).

Definition appr_cds_asp : Term := 
    (asp (ASPC (* ALL (EXTD 1) *) (asp_paramsC appr_cds_id [] P1 sys_targ))).

Definition sig_asp : Term := asp SIG.

Definition cds_demo_phrase : Term := 
<{
  @ P1 
  [
    (
    query_kim_asp -> (* +<+ *)
    meas_cds_phrase
     ) ->
    sig_asp
  ] -> 
  @ P3 [ appr_cds_asp ]
}>.


Print cds_demo_phrase.

Close Scope cop_ent_scope.


Definition cds_demo_arch_policy : CACL_Policy := 
    [
    (cds_exe_1_targ, [(in_targ, CACL_Read)]);

    (cds_exe_2_targ, [(tmp_1_targ, CACL_Read)]);
    (cds_exe_3_targ, [(tmp_2_targ, CACL_Read)]);
    (out_targ, [(tmp_3_targ, CACL_Read)]);
    (cds_exe_1_targ, [(tmp_1_targ, CACL_Write)]);
    (cds_exe_2_targ, [(tmp_2_targ, CACL_Write)]);
    (cds_exe_3_targ, [(tmp_3_targ, CACL_Write)]);

    (cds_exe_1_targ, [(cds_config_1_targ, CACL_Read)]);
    (cds_exe_2_targ, [(cds_config_2_targ, CACL_Read)]);
    (cds_exe_3_targ, [(cds_config_3_targ, CACL_Read)]);

    (cds_controller_exe_targ, [(cds_exe_dir_targ, CACL_Write)]);
    (cds_controller_exe_targ, [(cds_exe_dir_targ, CACL_Invoke)]);

    (cds_controller_exe_targ, [(cds_flags_dir_targ, CACL_Read)]);
    (cds_controller_exe_targ, [(cds_flags_dir_targ, CACL_Write)]);

    (cds_exe_1_targ, [(cds_flags_1_targ, CACL_Write)]);
    (cds_exe_2_targ, [(cds_flags_2_targ, CACL_Write)]);
    (cds_exe_3_targ, [(cds_flags_3_targ, CACL_Write)])
    ].


(*
Definition example_cacl_policy : CACL_Policy := 
    [(P1, [(attest_id, CACL_Invoke)]);
        (P2, [(appraise_id, CACL_Invoke);
            (certificate_id, CACL_Invoke)]);
        (attest_id, [(sys_targ, CACL_Read)])
        ].
*)
(* (CACL_policy_union example_cacl_policy example_cacl_policy). *)


Definition test_cacl_compute := 
    CACL_policy_union 
        cds_demo_arch_policy
        (CACL_policy_generator cds_demo_phrase P0).


(*
Definition test_cacl_compute_json : JSON := to_JSON test_cacl_compute.
*)

(*
Inductive EvidenceT :=
| mt_evt      : EvidenceT
| nonce_evt   : N_ID -> EvidenceT
| asp_evt     : Plc -> ASP_PARAMS -> EvidenceT -> EvidenceT
| left_evt    : EvidenceT -> EvidenceT
| right_evt   : EvidenceT -> EvidenceT
| split_evt   : EvidenceT -> EvidenceT -> EvidenceT.
*)

(*
Definition get_RawEv_snippet 
*)


Definition AppraisalSummary := (Map ASP_ID (Map TARG_ID string))%type.

Global Instance EqClass_RawEvJudgement : EqClass RawEv.
Admitted.

Definition RawEvJudgement := ASP_ID -> TARG_ID -> RawEv -> string.

Inductive Flat_EvidenceT :=
| flat_mt_evt      : Flat_EvidenceT
| flat_nonce_evt   : N_ID -> Flat_EvidenceT
| flat_asp_evt     : Plc -> ASP_PARAMS -> Flat_EvidenceT -> Flat_EvidenceT
| flat_split_evt   : Flat_EvidenceT -> Flat_EvidenceT -> Flat_EvidenceT.

Fixpoint flatten_EvidenceT (et:EvidenceT) : Flat_EvidenceT :=
    match et with
    | mt_evt => flat_mt_evt
    | nonce_evt nid => flat_nonce_evt nid
    | left_evt et' => flatten_EvidenceT et'
    | right_evt et' => flatten_EvidenceT et'
    | asp_evt p ps et' => flat_asp_evt p ps (flatten_EvidenceT et')
    | split_evt et1 et2 => flat_split_evt (flatten_EvidenceT et1) (flatten_EvidenceT et2)
    end.

Definition errStr_peel_n_am : string := "hi".

Fixpoint peel_n_rawev (n : nat) (ls : RawEv) : ResultT (RawEv * RawEv) string :=
    match n with
    | 0 => resultC ([], ls)
    | S n' =>
        match ls with
        | [] => errC errStr_peel_n_am
        | x :: ls' =>
        match peel_n_rawev n' ls' with
        | errC e => errC e
        | resultC (ls1, ls2) => resultC (x :: ls1, ls2)
        end
        end
    end.

Definition peel_n_rawev_noFail (n : nat) (ls : RawEv) : (RawEv * RawEv) := 
    match peel_n_rawev n ls with 
    | resultC res => res 
    | _ => ([],[])
    end.

Definition et_size_noFail (G:GlobalContext) (et:EvidenceT) : nat := 
    match (et_size G et) with 
    | resultC n => n 
    | _ => O 
    end.

Definition add_asp_summary (i:ASP_ID) (tid:TARG_ID) (m:RawEvJudgement) (rEv:RawEv)(s:AppraisalSummary) : AppraisalSummary := 
    let s := (m i tid rEv) in 
    ((i, tid), (f rEv)) :: s.

(*
    match (map_get (i, tid) m) with 
    | Some f => ((i, tid), (f rEv)) :: s
    | _ => []
    end.
    *)


(* TODO:  make this a ResultT type eventually to fail on map lookup? *)
Fixpoint get_AppraisalSummary' (et:EvidenceT) (r:RawEv) (G:GlobalContext) (m:RawEvJudgement) (s:AppraisalSummary) : AppraisalSummary := 
        match et with 
        | mt_evt => [] 
        | nonce_evt nid => s (* TODO:  do anything else with nonce check here? *)
        | split_evt et1 et2 => 
            let (r1, rest) := peel_n_rawev_noFail (et_size_noFail G et1) r in
            let (r2, _) := peel_n_rawev_noFail (et_size_noFail G et2) rest in

            let s1 := get_AppraisalSummary' et1 r1 G m s in 
            let s2 := get_AppraisalSummary' et2 r2 G m s1 in
                s2
        | left_evt et' => get_AppraisalSummary' et' r G m s
        | right_evt et' => get_AppraisalSummary' et' r G m s
        | asp_evt p ps et' => 
            let '(asp_paramsC asp_id args tp tid) := ps in 
                match (map_get asp_id (asp_types G)) with 
                | None => s  (* TODO: resultT type eventually... *)
                | Some (ev_arrow fwd in_sig out_sig) => 
                    match fwd with 
                    | REPLACE => 
                        match out_sig with 
                        | OutN n => 
                            let (r1, rest) := peel_n_rawev_noFail n r in 
                            let s' := add_asp_summary asp_id tid m r1 s in
                                get_AppraisalSummary' et' rest G m s'
                        | _ => s
                        end
                    (*
                    | WRAP => 
                        match out_sig with 
                        | OutN n => 
                            let (r1, rest) := peel_n_rawev_noFail n r in 
                            let s' := add_asp_summary asp_id tid m r1 s in
                                get_AppraisalSummary' et' rest G m s'
                        | _ => s
                        end 
                    *)

                    | EXTEND => 
                        match out_sig with 
                        | OutN n => 
                            let (r1, rest) := peel_n_rawev_noFail n r in 
                            let s' := add_asp_summary asp_id tid m r1 s in
                                get_AppraisalSummary' et' rest G m s'
                        | _ => s
                        end
                        
                    | _ => s
                    end

                end

        end.

Definition get_AppraisalSummary (et:EvidenceT) (r:RawEv) (G:GlobalContext) (m:RawEvJudgement) : AppraisalSummary := 
    get_AppraisalSummary' et r G m [].

Open Scope string_scope.

Definition hi_id : ASP_ID := "hi".
Definition hey_id : TARG_ID := "hey".
Definition howdy_string : string := "howdy".

Definition example_appraisal_summary := (hi_id, hey_id, howdy_string).
Check example_appraisal_summary.

(*
Global Instance AppraisalSummaryJsonifiable `{Stringifiable (ASP_ID * TARG_ID)%type, Stringifiable string} : Jsonifiable (list ((ASP_ID * TARG_ID) * string)).
eapply Build_Jsonifiable with 
    (to_JSON := map_serial_serial_to_JSON)
    (from_JSON := map_serial_serial_from_JSON).
    intros.
    rewrite canonical_jsonification_map_serial_serial in *.
    eauto.
Qed.
*)

Definition pair_to_string {A B : Type} `{Stringifiable A, Stringifiable B} (v : (A * B)) : string :=
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

Global Instance StringifiableAppraisalSummary' : Stringifiable (ASP_ID * TARG_ID). 

Global Instance AppraisalSummaryJsonifiable `{Stringifiable (ASP_ID * TARG_ID)%type} : Jsonifiable AppraisalSummary.
eapply Build_Jsonifiable with 
(to_JSON := map_serial_serial_to_JSON)
(from_JSON := map_serial_serial_from_JSON).
intros.
rewrite canonical_jsonification_map_serial_serial in *.
eauto.
Qed.



Definition test_app_summary_compute_json `{Stringifiable (ASP_ID * TARG_ID)%type} (x:AppraisalSummary) : JSON := to_JSON x.

(*

Example fdfd : forall (x:AppraisalSummary), x = example_appraisal_summary.

Check example_appraisal_summary.
*)

