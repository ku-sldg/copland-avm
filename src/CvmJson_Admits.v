Require Import Term_Defs.

Definition JsonT : Set. Admitted.

Definition jsonToCvmIn (j:JsonT) : CvmInMessage.
Admitted.

Definition jsonToCvmOut (j:JsonT) : CvmOutMessage.
Admitted.

Definition cvmInMessageToJson (cvmin:CvmInMessage) : JsonT.
Admitted.

Definition cvmOutMessageToJson (cvmout:CvmOutMessage): JsonT.
Admitted.