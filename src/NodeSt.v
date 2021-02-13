Require Import Term_Defs ConcreteEvidence.

Require Import StructTact.Update.

Inductive Prim_Instr: Set :=
| copy: Prim_Instr
| umeas: ASP_ID -> list Arg -> Prim_Instr
| sign: Prim_Instr
| hash: Prim_Instr.

Inductive AnnoInstr{n:nat}: Type :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| aReq: nat -> nat -> (fin n) -> AnnoInstr
| aseq: AnnoInstr -> AnnoInstr -> AnnoInstr.

Definition asp_instr (a:ASP) : Prim_Instr :=
  match a with
  | CPY => copy
  | ASPC i args => umeas i args
  | SIG => sign
  | HSH => hash
  end.

Fixpoint instr_compiler{n:nat} (t:@AnnoTerm n) : AnnoInstr :=
  match t with
  | aasp (i,_) a => aprimInstr i (asp_instr a)
  | aatt (i,j) p q _ =>
    (aReq i (Nat.pred j) q)
  | alseq _ t1 t2 => aseq (instr_compiler t1) (instr_compiler t2)
  end.

Definition tr_asp_instr{n:nat} (x:nat) (p:fin n) (pi:Prim_Instr) :=
  match pi with
  | copy => Term_Defs.copy x p
  | umeas asp_id args => (Term_Defs.umeas x p asp_id args)
  | sign => Term_Defs.sign x p
  | hash => Term_Defs.hash x p
  end.





