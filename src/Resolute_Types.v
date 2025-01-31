Require Import Term_Defs Resolute_Logic. (* Attestation_Session AppraisalSummary. *)
(* Require Export Interface_Strings_Vars. *)


Record ResoluteResponse := 
    mkResoluteResp {
      resoluteresp_success: bool;
      resoluteresp_formula: Resolute_Formula;
      resoluteresp_term: Term;
  }.
