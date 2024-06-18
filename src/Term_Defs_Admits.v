Require Import Term_Defs_Core Term_Defs ResultT StringT.

Fixpoint Term_to_stringT (t : Term) : StringT. Admitted.
Definition stringT_to_Term (s : StringT) : ResultT Term StringT. Admitted.

Definition Evidence_to_stringT (e:Evidence) : StringT. Admitted.
Definition stringT_to_Evidence (s:StringT) : ResultT Evidence StringT. Admitted.

Fixpoint AppResultC_to_stringT (res: AppResultC) : StringT. Admitted.
Definition stringT_to_AppResultC (s: StringT) : ResultT AppResultC StringT. Admitted.

Definition RawEv_to_stringT (e:RawEv) : StringT. Admitted.
Definition stringT_to_RawEv (s:StringT) : ResultT RawEv StringT. Admitted.

Definition EvC_to_stringT (e:EvC) : StringT. Admitted.
Definition stringT_to_EvC (s:StringT) : ResultT EvC StringT. Admitted.

Fixpoint Ev_to_stringT (e:Ev) : StringT. Admitted.
Definition stringT_to_Ev (s:StringT) : ResultT Ev StringT. Admitted.

Definition ASP_ARGS_to_stringT (args:ASP_ARGS) : StringT. Admitted.
Definition stringT_to_ASP_ARGS (s:StringT) : ResultT ASP_ARGS StringT. Admitted.