Require Import Term LTS.
Require Import More_lists Preamble List.
Import ListNotations.
Set Nested Proofs Allowed.

  

(** * VM Instructions *)

Inductive Prim_Instr: Set :=
| copy: Prim_Instr
(* | kmeas: ASP_ID -> Plc -> (list Arg) -> Prim_Instr *)
| umeas: ASP_ID -> Prim_Instr
| sign: Prim_Instr
| hash: Prim_Instr.

Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| asplit: nat -> SP -> SP -> AnnoInstr
| ajoins: nat -> AnnoInstr
| ajoinp: nat -> nat -> nat -> AnnoInstr
| abesr : AnnoInstr 
(*| areq: nat -> Plc -> AnnoTerm -> AnnoInstr
| arpy: nat -> nat -> Plc -> AnnoInstr *)
| areqrpy: nat -> nat -> Plc -> AnnoTerm -> AnnoInstr  (* TODO: update rest of spec *)
| abep: nat -> nat ->
        (list AnnoInstr) -> (list AnnoInstr) -> AnnoInstr.

(** * Instruction Compiler *)
Definition asp_instr (a:ASP) : Prim_Instr :=
  match a with
  | CPY => copy
(*  | KIM i p args => kmeas i p args *)
  | ASPC i => umeas i
  | SIG => sign
  | HSH => hash
  end.

Fixpoint instr_compiler (t:AnnoTerm) : (list AnnoInstr) :=
  match t with
  | aasp r a => [aprimInstr (fst r) (asp_instr a)]  
  | aatt r q t' =>
    let '(reqi,rpyi_last) := r in
    [areqrpy reqi rpyi_last q t']
    (*[areq (fst r) q t'] ++ [arpy (Nat.pred rpyi_last) (fst r)  q]*)           
  | alseq _ t1 t2 =>
    let tr1 := instr_compiler t1 in
    let tr2 := instr_compiler t2 in
    tr1 ++ tr2     
  | abseq r (sp1,sp2) t1 t2 =>
    let tr1 := instr_compiler t1 in
    let tr2 := instr_compiler t2 in
    let i := Nat.pred (snd r) in
    [asplit (fst r) sp1 sp2] ++ tr1 ++ [abesr] ++ tr2 ++ [ajoins i]
  | abpar r (sp1,sp2) t1 t2 =>
    (*let splEv := [split sp1 sp2] in*)
    let tr1 := instr_compiler t1 in
    let tr2 := instr_compiler t2 in
    let store_loc1 := (fst (range t1)) in
    let store_loc2 := (fst (range t2)) in
    let tr := [abep store_loc1 store_loc2 tr1 tr2] in
    let i := Nat.pred (snd r) in
    [asplit (fst r) sp1 sp2] ++ tr ++ [ajoinp i store_loc1 store_loc2 ]
  end.