(*  Implementation of a top-level Server (listener) thread for Server AMs in
      end-to-end Copland Attestation + Appraisal protocols.  *)
Require Import StringT BS Manifest CvmJson_Interfaces AM_Helpers AM_Json_Interfaces.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition handle_AM_request (s:StringT) (ac : AM_Config) (al:AM_Library) (nonceVal:BS) : StringT :=
  match strToJson s with
  | None => jsonToStr (ErrorResponseJson "Invalid JSON")
  | Some js => jsonToStr (handle_AM_request_Json js ac al nonceVal)
  end.
