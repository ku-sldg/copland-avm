(** Core EvidenceT bundling operations internal to the CVM.  
    Each updates the raw EvidenceT sequence (compacting, extending, etc.),
    along with a principled update to its corresponding EvidenceT Type.

    Matching on the EvidenceT Type param is only for verification.  
    Extracted code could be simplified to only the raw EvidenceT operation. *)
Require Import List String.

Require Import Term_Defs ResultT ErrorStringConstants EqClass.

Import ListNotations.

(* The semantics for a "REPLACE" asp are it CONSUMES all incoming evidence,
then returns a new collection of evidence that will REPLACE the CVMs current 
Evidence *)
Definition REPLACE_bundle (bits: RawEv) (e:Evidence) (p:Plc) 
    (ps:ASP_PARAMS): ResultT Evidence string :=
  match e with
  | evc _ et => resultC (evc bits (asp_evt p ps et))
  end.

(* The semantics for a "WRAP" asp are the exact same as "REPLACE" for the 
attestation and bundling side of the CVM. Wraps main distinction lies in the
fact that its is a GUARANTEE, that the dual appraisal ASP is actually an
inverse, thus allowing WRAPPED evidence to be recovered via appraisal *)
Definition WRAP_bundle (bits: RawEv) (e:Evidence) (p:Plc) 
    (ps:ASP_PARAMS): ResultT Evidence string :=
  match e with
  | evc _ et => resultC (evc bits (asp_evt p ps et))
  end.

(* The semantics for an "EXTEND" asp are it APPENDS all incoming evidence to the
current CVM evidence bundle *)
Definition EXTEND_bundle (sig: RawEv) (e:Evidence) (p:Plc) (n : nat) 
    (ps:ASP_PARAMS): ResultT Evidence string :=
  match e with
  | evc bits et => 
      if (eqb (List.length sig) n)
      then resultC (evc (sig ++ bits) (asp_evt p ps et))
      else errC errStr_raw_EvidenceT_too_long
  end.
(* 
(** Collapses raw EvidenceT by replacing the entire sequence with the input 
    binary hash value.  Updates underlying EvidenceT Type to reflect the hash. *)
Definition comp_bundle (hsh: RawEv) (e:Evidence) (p:Plc) (ps:ASP_PARAMS): ResultT Evidence string :=
  match e with
  | evc _ et => 
    match hsh with
    | [] => errC errStr_empty_raw_ev
    | [h] => resultC (evc [h] (asp_evt p ps et))
    | _ => errC errStr_raw_EvidenceT_too_long
    end
  end.

(** Collapses raw EvidenceT by replacing the entire sequence with the input 
    encrypted value blob.  Updates underlying EvidenceT Type to reflect the
    encryption. *)
Definition encr_bundle (enc: RawEv) (e:Evidence) (p:Plc) (ps:ASP_PARAMS): ResultT Evidence string :=
  match e with
  | evc _ et => 
    match enc with
    | [] => errC errStr_empty_raw_ev
    | [h] => resultC (evc [h] (asp_evt p ps et))
    | _ => errC errStr_raw_EvidenceT_too_long
    end
  end. *)

(** Appends raw EvidenceT and EvidenceT Types for the pair of input bundles *)
Definition ss_cons (e1:Evidence) (e2:Evidence): Evidence :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (split_evt et1 et2)
  end.
