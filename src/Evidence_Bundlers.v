(** Core evidence bundling operations internal to the CVM.  
    Each updates the raw evidence sequence (compacting, extending, etc.),
    along with a principled update to its corresponding Evidence Type.

    Matching on the Evidence Type param is only for verification.  
    Extracted code could be simplified to only the raw evidence operation. *)

Require Import ConcreteEvidence IO_Stubs.

Require Import List.

Import ListNotations.

(* Helper that simulates encoding the raw bits portion of an evidence bundle.
   Note: encodeEvRaw is (as of now) an Admitted (abstract) operation.  *)
Definition encodeEvBits (e:EvC): BS :=
  match e with
  | (evc bits _) => encodeEvRaw bits
  end.

(** Extends raw evidence by prepending one value to the front.
    Also updates underlying Evidence Type.
    An example is digital signatures, where the signature value is prepended *)
Definition cons_gg (sig:BS) (e:EvC) (p:Plc) (ps:ASP_PARAMS): EvC :=
  match e with
  | evc bits et => evc (sig :: bits) (uu p EXTD ps et)
  end.

(** Collapses raw evidence by replacing the entire sequence with the input 
    binary hash value.  Updates underlying Evidence Type to reflect the hash. *)
Definition cons_hsh (hsh:BS) (e:EvC) (p:Plc) (ps:ASP_PARAMS): EvC :=
  match e with
  | evc _ et => evc [hsh] (uu p COMP ps et)
  end.

(** Collapses raw evidence by replacing the entire sequence with the input 
    encrypted value blob.  Updates underlying Evidence Type to reflect the
    encryption. *)
Definition cons_enc (enc:BS) (e:EvC) (p:Plc) (ps:ASP_PARAMS): EvC :=
  match e with
  | evc _ et => evc [enc] (uu p ENCR ps et)
  end.

(** Appends raw evidence and Evidence Types for the pair of input bundles *)
Definition ss_cons (e1:EvC) (e2:EvC): EvC :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (ss et1 et2)
  end.
