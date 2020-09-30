Require Import More_lists Preamble Term LTS.
Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

  
(** * VM Instructions *)

Inductive Prim_Instr: Set :=
| copy: Prim_Instr
| umeas: ASP_ID -> Prim_Instr
| sign: Prim_Instr
| hash: Prim_Instr.

Inductive AnnoInstr: Set :=
| aprimInstr: nat -> Prim_Instr -> AnnoInstr
| asplit: nat -> SP -> SP -> AnnoInstr
| ajoins: nat -> AnnoInstr
| ajoinp: nat -> nat -> nat -> AnnoInstr
| abesr : AnnoInstr 
| areqrpy: nat -> nat -> Plc -> AnnoTerm -> AnnoInstr
| abep: nat -> nat ->
        (list AnnoInstr) -> (list AnnoInstr) -> AnnoInstr.

(** * Instruction Compiler *)
Definition asp_instr (a:ASP) : Prim_Instr :=
  match a with
  | CPY => copy
  | ASPC i => umeas i
  | SIG => sign
  | HSH => hash
  end.

Fixpoint instr_compiler (t:AnnoTerm) : (list AnnoInstr) :=
  match t with
  | aasp r a => [aprimInstr (fst r) (asp_instr a)]  
  | aatt (i,j) q t' => [areqrpy i j q t']      
  | alseq _ t1 t2 => (instr_compiler t1) ++ (instr_compiler t2)     
  | abseq (i,j) (sp1,sp2) t1 t2 =>
    [asplit i sp1 sp2] ++
    (instr_compiler t1) ++ [abesr] ++ (instr_compiler t2) ++
    [ajoins (Nat.pred j)]
  | abpar (i,j) (sp1,sp2) t1 t2 =>
    let store_loc1 := (fst (range t1)) in
    let store_loc2 := (fst (range t2)) in  
    [asplit i sp1 sp2] ++
    [abep store_loc1 store_loc2 (instr_compiler t1) (instr_compiler t2)] ++
    [ajoinp (Nat.pred j) store_loc1 store_loc2 ]
  end.

Inductive is_compiled_list : (list AnnoInstr) -> Prop :=
| primList : forall n i, is_compiled_list [(aprimInstr n i)]
| atList : forall i j q t, is_compiled_list [(areqrpy i j q t)]
| linList : forall il1 il2, is_compiled_list il1 -> is_compiled_list il2 -> is_compiled_list (il1 ++ il2)
| bseqList : forall il1 il2 i sp1 sp2 j, is_compiled_list il1 -> is_compiled_list il2 ->
                                    is_compiled_list ([asplit i sp1 sp2] ++ il1 ++ [abesr] ++ il2 ++ [ajoins j])
| brparList : forall il1 il2 i sp1 sp2 j loc1 loc2, is_compiled_list il1 -> is_compiled_list il2 ->
                                               is_compiled_list ([asplit i sp1 sp2] ++ [abep loc1 loc2 il1 il2] ++ [ajoinp j loc1 loc2]).

Lemma compile_ind : forall t, is_compiled_list (instr_compiler t).
Proof.
  intros.
  induction t;
    try ( destruct a; simpl; econstructor).
  - destruct r. simpl. econstructor.
  - simpl.
    econstructor; eauto.
  - destruct r. destruct s. simpl.
    econstructor; eauto.
  - destruct r. destruct s. simpl.
    econstructor; eauto.
Defined.
