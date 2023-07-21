Require Import Term_Defs.

Definition JsonT : Set. Admitted.

Definition StringT: Set. Admitted.

Definition strToJson (s:StringT): JsonT.
Admitted.

Definition jsonToCvmIn (j:JsonT) : CvmInMessage.
Admitted.

Definition jsonToCvmOut (j:JsonT) : CvmOutMessage.
Admitted.

Definition cvmInMessageToJson (cvmin:CvmInMessage) : JsonT.
Admitted.

Definition cvmOutMessageToJson (cvmout:CvmOutMessage): JsonT.
Admitted.

Definition requestToJson (req:CvmRequestMessage): JsonT.
Admitted.

Definition responseToJson (resp:CvmResponseMessage): JsonT.
Admitted.

Definition jsonToRequest (j:JsonT) : CvmRequestMessage.
Admitted.

Definition jsonToResponse (j:JsonT) : CvmRequestMessage.
Admitted.

