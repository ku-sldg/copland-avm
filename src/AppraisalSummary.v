Require Import Term_Defs Maps ID_Type EqClass JSON ErrorStringConstants.

Require Import CACL_Defs CACL_Typeclasses CACL_Demo.

Require Import Cvm_Utils RawEvJudgement_Admits.

Require Import List.
Import ListNotations.

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
        | left_evt et' => 
            r <- apply_to_evidence_below G (fun et'' => do_AppraisalSummary' et'' r G m s) [Trail_LEFT] et' ;;
            r
        (* do_AppraisalSummary' et' r G m s *)
        
        | right_evt et' => 
            r <- apply_to_evidence_below G (fun et'' => do_AppraisalSummary' et'' r G m s) [Trail_RIGHT] et' ;;
            r
        (* do_AppraisalSummary' et' r G m s *)
        
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
                    
                       (* 
                    | _ => resultC s *)
                    
                    | REPLACE => 
                        match out_sig with 
                        | OutN n => 
                            let f := get_RawEvJudgement i tid m in 
                            '(r1, rest) <- peel_n_rawev n r ;; 
                            let s' := add_asp_summary i tid f r1 s in 
                            resultC s'
                            (*
                            do_AppraisalSummary' et' rest G m s'
                            *)

                        | _ => errC err_str_cannot_have_outwrap
                        end

                    | _ => resultC s 

                    (*
                        match out_sig with 
                        | OutN n => 
                            let (r1, rest) := peel_n_rawev_noFail n r in 
                            let s' := add_asp_summary asp_id tid m r1 s in
                                do_AppraisalSummary' et' rest G m s'
                        | _ => s
                        end
                        *)
                    (*
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

Definition single_add_type := (ASP_ID * (TARG_ID * (RawEv -> string)))%type.

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
        (appr_gather_file_contents_id, (cds_config_3_targ, ex_targJudgement_fun'));
        (appr_query_kim_id, (kim_evidence_targ, ex_targJudgement_fun'));
        (appr_hash_file_contents_id, (cds_img_1_targ, ex_targJudgement_fun'));
        (appr_hash_file_contents_id, (cds_img_2_targ, ex_targJudgement_fun'));
        (appr_hash_file_contents_id, (cds_img_3_targ, ex_targJudgement_fun'));
        (appr_query_kim_stub_id, (kim_evidence_targ, ex_targJudgement_fun'));
        (r_ssl_sig_appr_id, (ssl_sig_targ, ex_targJudgement_fun'));
        (tpm_sig_appr_id, (ssl_sig_targ, ex_targJudgement_fun'));
        (appr_selinux_pol_dump_id, (cds_img_2_targ, ex_targJudgement_fun'))
    ].


Definition example_RawEvJudgement : RawEvJudgement := 
    gen_rawEvJudgement example_RawEvJudgement_ls.


Definition cds_RawEvJudgement_ls : list single_add_type := 
    [
        (appr_gather_file_contents_id, (cds_config_1_targ, ex_targJudgement_fun'));
        (appr_gather_file_contents_id, (cds_config_2_targ, ex_targJudgement_fun'));
        (appr_query_kim_id, (kim_evidence_targ, ex_targJudgement_fun'));
        (appr_hash_file_contents_id, (cds_img_1_targ, ex_targJudgement_fun'));
        (appr_hash_file_contents_id, (cds_img_2_targ, ex_targJudgement_fun'));
        (r_ssl_sig_appr_id, (ssl_sig_targ, ex_targJudgement_fun'));
        (tpm_sig_appr_id, (tpm_sig_targ, ex_targJudgement_fun'));
        (appr_selinux_pol_dump_id, (selinux_policy_targ, ex_targJudgement_fun'))
    ].

Definition cds_RawEvJudgement : RawEvJudgement := 
    gen_rawEvJudgement cds_RawEvJudgement_ls.

Global Instance AppraisalSummaryJsonifiable `{Stringifiable ASP_ID, Stringifiable (Map TARG_ID string)} : Jsonifiable AppraisalSummary.
eapply Build_Jsonifiable with 
(to_JSON := map_serial_serial_to_JSON)
(from_JSON := map_serial_serial_from_JSON).
intros.
rewrite canonical_jsonification_map_serial_serial in *.
eauto.
Qed.

Definition test_app_summary_compute_json (x:AppraisalSummary) : JSON := to_JSON x.