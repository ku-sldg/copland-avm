(* Admitted definitions of JSON types and conversions to/from strings 
    and Copland datatypes at the boundary of AMs.
    
    At the moment, these are too low-level to represent faithfully in the Coq development.   *)

Require Import Term_Defs_Core Term_Defs StringT List.
From JSON Require Import JSON Lexer Printer.
Import ListNotations.

Definition strToJson (s:StringT): option json := 
  match from_string (StringT_to_string s) with
  | inl e => None
  | inr j => Some j
  end.

Definition jsonToStr (js: json): StringT := 
  string_to_StringT (to_string js).

Definition ProtocolRunRequest_to_Json (req: ProtocolRunRequest): json :=
  JSON__Object 
    [("term", (JSON__String (Term_to_string (prreq_term req)))); 
    ("authTok", (JSON__String (EvC_to_string (prreq_authTok req)))); 
    ("ev", (JSON__String (RawEv_to_string (prreq_ev req))))].

Definition ProtocolRunResponse_to_Json (resp: ProtocolRunResponse): json :=
  JSON__Object 
    [("success", (if (prresp_success resp) then JSON__True else JSON__False));
    ("ev", (JSON__String (RawEv_to_string (prresp_ev resp))))].

Definition responseToJson (resp: ProtocolRunResponse): JsonT.
Admitted.

Definition amRequestToJson (req:AM_RequestMessage): JsonT.
Admitted.

Definition appResponseToJson (resp:ProtocolAppraiseResponse): JsonT.
Admitted.

Definition jsonToRequest (j:JsonT) : ProtocolRunRequest.
Admitted.

Definition jsonToResponse (j:JsonT) : ProtocolRunRequest.
Admitted.

Definition jsonToAmRequest (j:JsonT): AM_RequestMessage.
Admitted.