Require Import ConcreteEvidence IO_Stubs.

Require Import List.
Import ListNotations.

(* Matches on evidence type param only for verification.  
   Will extract to the cons function over the first two params (new measurement bits + existing evidence) *)

(*
Definition cons_uu (x:BS) (e:EvC) (*(i:ASP_ID) (args:list Arg) (tpl:Plc) (tid:TARG_ID) (tet:Evidence)*)(params:ASP_PARAMS) (mpl:Plc) : EvC :=
  match e with
  | evc bits et => evc (x :: bits) (uu params(*i args tpl tid tet*) mpl et)
  end.
*)

Definition cons_gg (sig:BS) (e:EvC) (p:Plc) (ps:ASP_PARAMS): EvC :=
  match e with
  | evc bits et => evc (sig :: bits) (gg p ps et)
  end.

Definition cons_hh (hsh:BS) (e:EvC) (p:Plc) (ps:ASP_PARAMS): EvC :=
  match e with
  | evc _ et => evc [hsh] (hh p ps et)
  end.

Definition ss_cons (e1:EvC) (e2:EvC): EvC :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (ss et1 et2)
  end.

(*

Definition pp_cons (e1:EvC) (e2:EvC): EvC :=
  match (e1, e2) with
  | (evc bits1 et1, evc bits2 et2) => evc (bits1 ++ bits2) (pp et1 et2)
  end.
*)

Definition encodeEvBits (e:EvC): BS :=
  match e with
  | (evc bits _) => encodeEvRaw bits
  end.
