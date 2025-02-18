Require Import Term_Defs Resolute_Logic. (* Attestation_Session AppraisalSummary. *)
(* Require Export Interface_Strings_Vars. *)


Record ResoluteResponse := 
    mkResoluteResp {
      resoluteresp_judgement: Resolute_Judgement;
      resoluteresp_formula: Resolute_Formula;
      resoluteresp_term: Resolute_Term;
  }.
