Require Import Term_Defs_Core Term_Defs ResultT String.

Fixpoint Term_to_string (t : Term) : string. Admitted.
Definition string_to_Term (s : string) : ResultT Term string. Admitted.

Definition Evidence_to_string (e:Evidence) : string. Admitted.
Definition string_to_Evidence (s:string) : ResultT Evidence string. Admitted.

Fixpoint AppResultC_to_string (res: AppResultC) : string. Admitted.
Definition string_to_AppResultC (s: string) : ResultT AppResultC string. Admitted.

Definition RawEv_to_string (e:RawEv) : string. Admitted.
Definition string_to_RawEv (s:string) : ResultT RawEv string. Admitted.

Definition EvC_to_string (e:EvC) : string. Admitted.
Definition string_to_EvC (s:string) : ResultT EvC string. Admitted.

Fixpoint Ev_to_string (e:Ev) : string. Admitted.
Definition string_to_Ev (s:string) : ResultT Ev string. Admitted.

Definition ASP_ARGS_to_string (args:ASP_ARGS) : string. Admitted.
Definition string_to_ASP_ARGS (s:string) : ResultT ASP_ARGS string. Admitted.