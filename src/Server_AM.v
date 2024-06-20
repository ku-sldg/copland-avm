(*  Implementation of a top-level Server (listener) thread for Server AMs in
      end-to-end Copland Attestation + Appraisal protocols.  *)
Require Import StringT BS Manifest CvmJson_Interfaces AM_Helpers AM_Json_Interfaces.
Require Import List ResultT.
Import ListNotations.
Open Scope string_scope.

Definition handle_AM_request (s:StringT) (ac : AM_Config) (nonceVal:BS) : StringT :=
  match stringT_to_JSON s with
  | errC msg => JSON_to_stringT (ErrorResponseJSON msg)
  | resultC js => JSON_to_stringT (handle_AM_request_JSON js ac nonceVal)
  end.
