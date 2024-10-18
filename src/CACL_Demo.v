Require Import Term_Defs Maps ID_Type EqClass.

Require Import Manifest_Set JSON JSON_Core ErrorStringConstants.

Require Import Flexible_Mechanisms_Vars.

Require Import CACL Cvm_Utils RawEvJudgement_Admits.

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
Definition gather_file_contents_id : ASP_ID := "r_readfile_id". (* "gather_file_contents_id" *)
Definition appr_gather_file_contents_id : ASP_ID := "appraise_r_readfile_id".
Definition appr_cds_id : ASP_ID := "appr_cds_id".






Definition gather_targ_asp (targPlc:Plc) (targId:TARG_ID) (path:string) : Term := 
    (asp (ASPC (* ALL (EXTD 1)  *)
               (asp_paramsC 
                    gather_file_contents_id 
                    [("filepath", path)] 
                    targPlc 
                    targId ))).

Definition hash_targ_asp (targPlc:Plc) (targId:TARG_ID) : Term := 
    (asp (ASPC (* ALL (EXTD 1) *)
                (asp_paramsC 
                    hash_file_contents_id 
                    [] 
                    targPlc 
                    targId ))).


Close Scope string_scope.


Open Scope cop_ent_scope.

Definition path_targ1 : string := "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/targFile.txt".

Definition path_targ2 : string := "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/targFile2.txt".

Definition path_targ3 : string := "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/targFile3.txt".

Definition gather_config_1 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_1_targ path_targ1).

Definition gather_config_2 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_2_targ path_targ2).

Definition gather_config_3 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_3_targ path_targ3).

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


Definition AppraisalSummary := (Map ASP_ID (Map TARG_ID string)).

Definition RawEvJudgement := Map ASP_ID (Map TARG_ID (RawEv -> string)).

Definition add_RawEvJudgement (i:ASP_ID) (tid:TARG_ID) (f:RawEv -> string) 
    (m:RawEvJudgement) : RawEvJudgement := 
    let m' := 
        match (map_get i m) with 
        | Some tm => tm
        | None => [] 
        end in 
    let m'' := map_set tid f m' in 
            map_set i m'' m.


Open Scope string_scope.

Definition get_RawEvJudgement (i:ASP_ID) (tid:TARG_ID) (m:RawEvJudgement) : (RawEv -> string) := 
    let default_fun := 
        (fun _ => "( " ++ i ++ ", " ++ tid ++ " ) " ++ "not found in RawEvJudgement map") in 
    
    match (map_get i m) with 
    | Some m' => 
        match (map_get tid m') with 
        | Some f => f 
        | None => default_fun
        end
    | None => default_fun
    end.

Definition map_get_default {A B:Type} `{H : EqClass A} (x:A) (y:B) (m:Map A B) : B := 
    match (map_get x m) with 
    | Some v => v 
    | None => y 
    end.

Definition set_AppraisalSummary (i:ASP_ID) (tid:TARG_ID) (str:string) 
    (s:AppraisalSummary) : AppraisalSummary := 
    let m := map_get_default i ([] : Map TARG_ID string) s in
    let m' := map_set tid str m in 
    map_set i m' s. 

Definition add_asp_summary (i:ASP_ID) (tid:TARG_ID) (f:(RawEv -> string)) (rEv:RawEv)
    (s:AppraisalSummary) : AppraisalSummary := 
    
        let str := f rEv in  
         set_AppraisalSummary i tid str s.

Import ResultNotation.

Fixpoint do_AppraisalSummary' (et:EvidenceT) (r:RawEv) (G:GlobalContext) 
    (m:RawEvJudgement) (s:AppraisalSummary) : ResultT AppraisalSummary string := 
        match et with 
        | mt_evt => resultC s 
        | nonce_evt nid => resultC s (* TODO:  do anything else with nonce check here? *)
        | split_evt et1 et2 => 
            et1_size <- et_size G et1 ;;
            et2_size <- et_size G et2 ;;
            '(r1, rest) <- peel_n_rawev et1_size r ;;
            '(r2, _) <- peel_n_rawev et2_size rest ;;
            s1 <- do_AppraisalSummary' et1 r1 G m s ;;
            do_AppraisalSummary' et2 r2 G m s1
        | left_evt et' => do_AppraisalSummary' et' r G m s
        | right_evt et' => do_AppraisalSummary' et' r G m s
        
        | asp_evt p ps et' => 
            let '(asp_paramsC i args tp tid) := ps in 
                match (map_get i (asp_types G)) with 
                | None => resultC s  (* TODO: resultT type eventually... *)
                | Some (ev_arrow fwd in_sig out_sig) => 
                    match fwd with 
                    
                    | EXTEND => 
                        match out_sig with 
                        | OutN n => 
                            let f := get_RawEvJudgement i tid m in 
                            '(r1, rest) <- peel_n_rawev n r ;; 
                            let s' := add_asp_summary i tid f r1 s in 
                            do_AppraisalSummary' et' rest G m s'

                        | _ => errC err_str_cannot_have_outwrap
                        end
                    
                        
                    | _ => resultC s
                    (*
                    | REPLACE => 
                        match out_sig with 
                        | OutN n => 
                            let (r1, rest) := peel_n_rawev_noFail n r in 
                            let s' := add_asp_summary asp_id tid m r1 s in
                                do_AppraisalSummary' et' rest G m s'
                        | _ => s
                        end
                    
                    | WRAP => 
                        match out_sig with 
                        | OutN n => 
                            let (r1, rest) := peel_n_rawev_noFail n r in 
                            let s' := add_asp_summary asp_id tid m r1 s in
                                do_AppraisalSummary' et' rest G m s'
                        | _ => s
                        end 
                    *)

                    end
                end

        end.

Definition do_AppraisalSummary (et:EvidenceT) (r:RawEv) (G:GlobalContext) (m:RawEvJudgement) : ResultT AppraisalSummary string := 
    do_AppraisalSummary' et r G m []. 

Open Scope string_scope.


Definition example_appTerm : Term := 
    (lseq gather_config_1 
        (lseq gather_config_2 
            (lseq gather_config_3 (asp APPR)))).


Check fold_left.

Definition single_add_type := (ASP_ID * (TARG_ID * (RawEv -> string)))%type.

(*
Definition add_RawEvJudgement (i:ASP_ID) (tid:TARG_ID) (f:RawEv -> string) 
    (m:RawEvJudgement) : RawEvJudgement := 
*)

Definition addOne_rawEvJudgement (a:RawEvJudgement) (b:single_add_type) : RawEvJudgement := 
    let aid := fst b in 
    let tid := fst (snd b) in 
    let f := snd (snd b) in 
    add_RawEvJudgement aid tid f a.

Definition gen_rawEvJudgement (ls:list single_add_type) : RawEvJudgement := 
    fold_left addOne_rawEvJudgement ls [].

Definition example_RawEvJudgement_ls : list single_add_type := 
    [
        (gather_file_contents_id, (cds_config_1_targ, ex_targJudgement_fun));
        (gather_file_contents_id, (cds_config_2_targ, ex_targJudgement_fun));
        (gather_file_contents_id, (cds_config_3_targ, ex_targJudgement_fun));
        (appr_gather_file_contents_id, (cds_config_1_targ, ex_targJudgement_fun'));
        (appr_gather_file_contents_id, (cds_config_2_targ, ex_targJudgement_fun'));
        (appr_gather_file_contents_id, (cds_config_3_targ, ex_targJudgement_fun'))
    ].


Definition example_RawEvJudgement : RawEvJudgement := 
    gen_rawEvJudgement example_RawEvJudgement_ls.



Global Instance AppraisalSummaryJsonifiable `{Stringifiable ASP_ID, Stringifiable (Map TARG_ID string)} : Jsonifiable AppraisalSummary.
eapply Build_Jsonifiable with 
(to_JSON := map_serial_serial_to_JSON)
(from_JSON := map_serial_serial_from_JSON).
intros.
rewrite canonical_jsonification_map_serial_serial in *.
eauto.
Qed.



Definition test_app_summary_compute_json (x:AppraisalSummary) : JSON := to_JSON x.

