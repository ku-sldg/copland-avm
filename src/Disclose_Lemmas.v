Require Import Term_Defs Anno_Term_Defs Term LTS Cvm_Impl Cvm_St Trace Main ConcreteEvidence.

Require Import CvmSemantics Appraisal_Evidence Eqb_Evidence Auto AbstractedTypes EqClass Helpers_CvmSemantics Disclose_Gen External_Facts Axioms_Io.

Require Import StructTactics.

Require Import ErrorStMonad_Coq.

Require Import Coq.Program.Tactics PeanoNat Lia.

Require Import List.
Import ListNotations.


(*
Lemma cvm_respects_term_disclosure_aspid:
  forall t p e i r atp bits bits' p' e' cvm_tr cvmi cvmi' annt ac ac',

    annoP_indexed annt t cvmi cvmi' ->

  ~ (term_discloses_aspid_to_remote t p e i r) ->
  
  term_to_coreP t atp ->
  build_cvmP atp
             (mk_st (evc bits e) [] p cvmi ac)
             (resultC tt)
             (mk_st (evc bits' e') cvm_tr p' cvmi' ac') ->

  ~ (cvm_trace_discloses_aspid_to_remote cvm_tr i r).
Proof.
    

*)

Definition term_discloses_aspid_to_remote_bool (t:Term) (p:Plc) (e:Evidence) (i:ASP_ID) (r:Plc) : bool.
Admitted.



(*
Definition term_discloses_aspid_to_remote (t:Term) (p:Plc) (e:Evidence) (i:ASP_ID) (r:Plc) : Prop :=
  let gen_aspid_evidence := (specific_aspid_genEvidence i) in
  exists et e',
    ((evidence_matches_gen gen_aspid_evidence et) = true) /\
    EvSubT et e' /\
    ((term_discloses_to_remote t p e (r,e')) = true).
    *)


(*
Fixpoint term_discloses_to_remote (t:Term) (p:Plc) (e:Evidence) (r:(Plc*Evidence)) : bool :=
  match t with
  | att q t' => (eqb_plc q (fst r)) && (eqb_evidence (snd r) e)(* (evsubt_bool (snd r) e) *) ||
               (term_discloses_to_remote t' q e r)
  | lseq t1 t2 => (term_discloses_to_remote t1 p e r) ||
                 (term_discloses_to_remote t2 p (eval t1 p e) r)
  | bseq (sp1,sp2) t1 t2 => (term_discloses_to_remote t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_remote t2 p (splitEv_mt sp2 e) r)
  | bpar (sp1,sp2) t1 t2 => (term_discloses_to_remote t1 p (splitEv_mt sp1 e) r) ||
                           (term_discloses_to_remote t2 p (splitEv_mt sp2 e) r)
  | _ => false
  end.
  *)




  (*
  
Definition cvm_trace_discloses_to_remote (tr:list Ev) (r:Plc) (e:Evidence) : Prop :=
  (* let gen_aspid_evidence := (specific_aspid_genEvidence i) in *)
  exists ev reqi p t (*e et*),
    (In ev tr) /\
    ev = (req reqi p r t e).

           (*
    /\
    (evidence_matches_gen gen_aspid_evidence et = true) /\
    evsubt_bool et e = true. *)

Definition cvm_trace_discloses_aspid_to_remote (tr:list Ev) (i:ASP_ID) (r:Plc) : Prop :=
  let gen_aspid_evidence := (specific_aspid_genEvidence i) in
  exists e et,
     (evidence_matches_gen gen_aspid_evidence et = true) /\
     evsubt_bool et e = true /\
     cvm_trace_discloses_to_remote tr r e.
     
     *)