Require Import Term_Defs Flexible_Mechanisms_Vars JSON_Type.

Require Import Demo_Terms CDS_Demo Rodeo_Demo Rodeo_Demo_NoArgs.
Require Import List String.
Import ListNotations.

(* Flexible Mechanisms *)
Definition certificate_style : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
      (att P2 (
        lseq 
          (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ)))
          (asp (ASPC (asp_paramsC certificate (JSON_Object []) P2 sys_targ)))
      ))
  ).

Definition background_check : Term :=
  lseq
    (att P1 (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ))))
    (att P2 (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ)))).

Definition parallel_mutual_1 : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
      (att P2 (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ))))
  ).

Definition layered_background_check : Term :=
  att P1
    (bpar (ALL, ALL)
      (lseq
        (att P1 (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ))))
        (lseq 
          (asp (ASPC (asp_paramsC attest (JSON_Object []) P3 sys_targ)))
          (asp (ASPC (asp_paramsC attest (JSON_Object []) P4 sys_targ)))
        )
      )
      (bpar (ALL, ALL)
        (att P3 (asp (ASPC (asp_paramsC attest (JSON_Object []) P3 sys_targ))))
        (lseq
          (att P4 (asp (ASPC (asp_paramsC attest (JSON_Object []) P4 sys_targ))))
          (att P2 (
            (lseq
              (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ)))
              (asp (ASPC sig_params))
            )
          )
          )
        )
      )
    ).

Definition filehash_auth_phrase : Term := 
  att P1 
    (lseq 
      (asp (ASPC (asp_paramsC hashfile (JSON_Object []) P1 sys_targ)))
      (asp SIG) 
    ).

Definition split_phrase : Term :=
  att P1 ( 
    bseq (ALL, ALL)
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
    ).

Definition large_output_asp_test : Term :=
  asp (ASPC (asp_paramsC large_output (JSON_Object []) P1 sys_targ)).


Open Scope string_scope.
Definition flexible_mechanisms_map : list (string * Term) := 
  [("cert", certificate_style); 
   ("cert_appr", lseq certificate_style (asp APPR)); 
   ("bg", background_check); 
   ("split", split_phrase);
   ("split_appr", lseq split_phrase (asp APPR));
   ("parmut", parallel_mutual_1); 
   ("layered_bg", layered_background_check); 
   ("filehash", filehash_auth_phrase);
   ("large_output", large_output_asp_test)].
Close Scope string_scope.

Definition full_terms_map := 
  List.app 
    flexible_mechanisms_map
    (
    List.app 
      cds_terms_map
      (
        List.app
          rodeo_terms_map
          rodeo_terms_noargs_map)).
   
Definition add_EvidenceT_terms_map (terms_map: list (string * Term)) : 
  GlobalContext -> Maps.Map string (Term * ResultT.ResultT EvidenceT string) := 
    fun G =>
    Maps.map_map (fun t => (t, eval G P0 mt_evt(* (nonce_evt 0) *) t)) terms_map.

Definition full_terms : 
  GlobalContext -> Maps.Map string (Term * ResultT.ResultT EvidenceT string) :=
    add_EvidenceT_terms_map full_terms_map.