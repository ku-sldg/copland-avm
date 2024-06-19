(** Core evidence bundling operations internal to the CVM.  
    Each updates the raw evidence sequence (compacting, extending, etc.),
    along with a principled update to its corresponding Evidence Type.

    Matching on the Evidence Type param is only for verification.  
    Extracted code could be simplified to only the raw evidence operation. *)

Require Import ConcreteEvidence IO_Stubs ResultT StringT ErrorStringConstants.

Require Import List.

Import ListNotations.

(** Extends raw evidence by prepending 'n' values to the front.
    Also updates underlying Evidence Type.
    An example is digital signatures, where the signature value is prepended *)
Definition extd_bundle (sig: RawEv) (e:EvC) (p:Plc) (n : nat) (ps:ASP_PARAMS): ResultT EvC StringT :=
  match e with
  | evc bits et => 
      if (Nat.eqb (length sig) n)
      then resultC (evc (sig ++ bits) (uu p (EXTD n) ps et))
      else errC errStr_raw_evidence_too_long
  end.

(** Collapses raw evidence by replacing the entire sequence with the input 
    binary hash value.  Updates underlying Evidence Type to reflect the hash. *)
Definition comp_bundle (hsh: RawEv) (e:EvC) (p:Plc) (ps:ASP_PARAMS): ResultT EvC StringT :=
  match e with
  | evc _ et => 
    match hsh with
    | [] => errC errStr_empty_raw_ev
    | [h] => resultC (evc [h] (uu p COMP ps et))
    | _ => errC errStr_raw_evidence_too_long
    end
  end.

(** Collapses raw evidence by replacing the entire sequence with the input 
    encrypted value blob.  Updates underlying Evidence Type to reflect the
    encryption. *)
Definition encr_bundle (enc: RawEv) (e:EvC) (p:Plc) (ps:ASP_PARAMS): ResultT EvC StringT :=
  match e with
  | evc _ et => 
    match enc with
    | [] => errC errStr_empty_raw_ev
    | [h] => resultC (evc [h] (uu p ENCR ps et))
    | _ => errC errStr_raw_evidence_too_long
    end
  end.

(** Appends raw evidence and Evidence Types for the pair of input bundles *)
Definition ss_cons (e1:EvC) (e2:EvC): EvC :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (ss et1 et2)
  end.
