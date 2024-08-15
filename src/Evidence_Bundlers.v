(** Core EvidenceT bundling operations internal to the CVM.  
    Each updates the raw EvidenceT sequence (compacting, extending, etc.),
    along with a principled update to its corresponding EvidenceT Type.

    Matching on the EvidenceT Type param is only for verification.  
    Extracted code could be simplified to only the raw EvidenceT operation. *)
Require Import List String.

Require Import ConcreteEvidenceT ResultT ErrorStringConstants EqClass.

Import ListNotations.

(** Extends raw EvidenceT by prepending 'n' values to the front.
    Also updates underlying EvidenceT Type.
    An example is digital signatures, where the signature value is prepended *)
Definition extd_bundle (sig: RawEv) (e:Evidence) (p:Plc) (n : nat) (ps:ASP_PARAMS): ResultT Evidence string :=
  match e with
  | evc bits et => 
      if (eqb (List.length sig) n)
      then resultC (evc (sig ++ bits) (asp_evt p (EXTD n) ps et))
      else errC errStr_raw_EvidenceT_too_long
  end.

(** Collapses raw EvidenceT by replacing the entire sequence with the input 
    binary hash value.  Updates underlying EvidenceT Type to reflect the hash. *)
Definition comp_bundle (hsh: RawEv) (e:Evidence) (p:Plc) (ps:ASP_PARAMS): ResultT Evidence string :=
  match e with
  | evc _ et => 
    match hsh with
    | [] => errC errStr_empty_raw_ev
    | [h] => resultC (evc [h] (asp_evt p COMP ps et))
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
    | [h] => resultC (evc [h] (asp_evt p ENCR ps et))
    | _ => errC errStr_raw_EvidenceT_too_long
    end
  end.

(** Appends raw EvidenceT and EvidenceT Types for the pair of input bundles *)
Definition ss_cons (e1:Evidence) (e2:Evidence): Evidence :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (split_evt et1 et2)
  end.
