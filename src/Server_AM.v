(*  Implementation of a top-level Server (listener) thread for Server AMs in
      end-to-end Copland Attestation + Appraisal protocols.  *)
Require Import String BS Attestation_Session Interface AM_Helpers AM_Json_Interfaces Manifest.
Require Import List ResultT.
Import ListNotations.
Open Scope string_scope.

Definition handle_AM_request (s:string) (m : Manifest) 
    (aspBin : FS_Location) (nonceVal:BS) : string :=
  match string_to_JSON s with
  | errC msg => JSON_to_string (ErrorResponseJSON msg)
  | resultC js => JSON_to_string (handle_AM_request_JSON js m aspBin nonceVal)
  end.


