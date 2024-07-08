(*  Implementation of a top-level Server (listener) thread for Server AMs in
      end-to-end Copland Attestation + Appraisal protocols.  *)
Require Import String BS Manifest CvmJson_Interfaces AM_Helpers AM_Json_Interfaces.
Require Import List ResultT.
Import ListNotations.
Open Scope string_scope.

Definition handle_AM_request (s:string) (ac : AM_Config) (nonceVal:BS) : string :=
  match string_to_JSON s with
  | errC msg => JSON_to_string (ErrorResponseJSON msg)
  | resultC js => JSON_to_string (handle_AM_request_JSON js ac nonceVal)
  end.
