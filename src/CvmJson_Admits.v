Require Import Term_Defs AM_Monad Impl_appraisal.

Definition JsonT : Set. Admitted.

Definition StringT: Set. Admitted.

Definition default_Json: JsonT.
Admitted.

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

(*
Definition run_appraisal_client (t:Term) (p:Plc) (e:Evidence) (re:RawEv) : AppResultC.
Admitted.
*)

(*
Definition run_appraisal_client (t:Term) (p:Plc) (e:Evidence) (re:RawEv) : AppResultC :=
    let expected_et := eval t p e in 
    let comp := gen_appraise_AM expected_et re in
    run_am_app_comp comp mtc_app.
*)