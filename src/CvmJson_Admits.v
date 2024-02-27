(* Admitted definitions of JSON types and conversions to/from strings 
    and Copland datatypes at the boundary of AMs.
    
    At the moment, these are too low-level to represent faithfully in the Coq development.   *)

Require Import Term_Defs StringT.

Definition JsonT : Set. Admitted.

Definition default_Json: JsonT.
Admitted.

Definition strToJson (s:StringT): JsonT.
Admitted.

Definition jsonToStr (js:JsonT): StringT.
Admitted.

Definition requestToJson (req:CvmRequestMessage): JsonT.
Admitted.

Definition responseToJson (resp:CvmResponseMessage): JsonT.
Admitted.

Definition amRequestToJson (req:AM_RequestMessage): JsonT.
Admitted.

Definition appResponseToJson (resp:AppraisalResponseMessage): JsonT.
Admitted.

Definition jsonToRequest (j:JsonT) : CvmRequestMessage.
Admitted.

Definition jsonToResponse (j:JsonT) : CvmRequestMessage.
Admitted.

Definition jsonToAmRequest (j:JsonT): AM_RequestMessage.
Admitted.