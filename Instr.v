Require Import Term.
Require Import MonadCOP.

Require Import List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.
Local Open Scope monad_scope.


(** * VM Instructions *)

Inductive Instr: Set :=
| copy: Instr
| kmeas: ASP_ID -> Plc -> (list Arg) -> Instr
| umeas: ASP_ID -> (list Arg) -> Instr
| sign: Instr
| hash: Instr
| reqrpy: Plc -> Plc -> Term -> Instr
| split: SP -> SP -> Instr
| besl: Instr -> Instr
| besr: Instr -> Instr
| bep: (list Instr) -> (list Instr) -> Instr
| joins: Instr
| joinp: Instr.

Definition eq_ev_dec:
  forall x y: Instr, {x = y} + {x <> y}.
Proof.
  intros.
  generalize dependent y.
  induction x;
    intros; destruct y; try (left; reflexivity); try (right; congruence).
  SearchAbout "eq_dec".
  destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  destruct (PeanoNat.Nat.eq_dec n n0);
    destruct (eq_ln_dec l l0); try (left; congruence); try (right; congruence).
  destruct (PeanoNat.Nat.eq_dec n n1);
    destruct (PeanoNat.Nat.eq_dec n0 n2);
    destruct (eq_term_dec t t0); try (left; congruence); try (right; congruence).
    destruct (eq_sp_dec s s1);
    destruct (eq_sp_dec s0 s2);
    try (left; congruence); try (right; congruence).
    destruct (IHx y); try (left; congruence); try (right; congruence).
    destruct (IHx y); try (left; congruence); try (right; congruence).
    admit.
Admitted.
Hint Resolve eq_ev_dec.

Definition eq_li_dec:
  forall x y: (list Instr), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.
Hint Resolve eq_li_dec.

Definition asp_instr (t:ASP) (p:Plc) : Instr :=
  match t with
  | CPY => copy
  | KIM i p args => kmeas i p args
  | USM i args => umeas i args
  | SIG => sign
  | HSH => hash
  end.

Fixpoint instr_compiler (t:Term) (p:Plc) : (list Instr) :=
  match t with
  | asp a => [asp_instr a p]
  | att q t' => [reqrpy p q t']
  | lseq t1 t2 =>
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    tr1 ++ tr2
  | bseq (sp1,sp2) t1 t2 =>
    let splEv := [split sp1 sp2] in
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    let evalL := map besl tr1 in
    let evalR := map besr tr2 in
    splEv ++ evalL ++ evalR ++ [joins]
  | bpar (sp1,sp2) t1 t2 =>
    let splEv := [split sp1 sp2] in
    let tr1 := instr_compiler t1 p in
    let tr2 := instr_compiler t2 p in
    let tr := [bep tr1 tr2] in
    splEv ++ tr ++ [joinp]
  end.

Fixpoint foldM_COP {A B : Type} (f:A -> B -> COP A) (a:A) (bs:list B) : COP A :=
  match bs with
  | [] => ret a
  | (x::xs) => f a x >>= fun fax => foldM_COP f fax xs
  end.

Definition invokeKIM (i:ASP_ID) (q:Plc) (args:list Arg) : COP BS.
Admitted.

Definition invokeUSM (i:ASP_ID) (args:list Arg) : COP BS.
Admitted.

Definition signEv (e:Evidence) : COP BS.
Admitted.

Definition hashEv (e:Evidence) : COP BS.
Admitted.

Definition toRemote (pTo:Plc) (t:Term) (e:Evidence) : COP Evidence.
Admitted.

Definition parallel_att_vm_thread (li:list Instr) (e:Evidence) : COP Evidence.
Admitted.

Definition splitEv (sp:SP) (e:Evidence) : Evidence :=
  match sp with
  | ALL => e
  | NONE => mt
  end.


Fixpoint vm_prim (e:Evidence) (instr:Instr) : COP Evidence :=
  p <- asks me ;;
    match instr with
    | copy => ret e
    | kmeas i q args =>
      bs <- invokeKIM i q args ;;
         ret (kk i args q p bs e)
    | umeas i args =>
      bs <- invokeUSM i args ;;
         ret (uu i args p bs e)
    | sign =>
      bs <- signEv e ;;
         ret (gg p e bs)
    | hash =>
      bs <- hashEv e ;;
         ret (hh p bs)
    | reqrpy _ pTo t =>
      toRemote pTo t e
    | split sp1 sp2 =>
      let e1 := splitEv sp1 e in
      let e2 := splitEv sp2 e in
      ret (sp e1 e2)
    | joins =>
      match e with
      | sp e1 e2 => ret (ss e1 e2)
      | _ => ret mt (* TODO: throw "bad stack" error? *)
      end
    | joinp =>
      match e with
      | sp e1 e2 => ret (pp e1 e2)
      | _ => ret mt (* TODO: throw "bad stack" error? *)
      end
    | besl ev' =>
      match e with
      | sp e1 e2 =>
        e1' <- vm_prim e1 ev' ;;
            ret (sp e1' e2)
      | _ => ret mt (* TODO: throw "bad stack" error? *)
      end
    | besr ev' =>
      match e with
      | sp e1 e2 =>
        e2' <- vm_prim e2 ev' ;;
            ret (sp e1 e2')
      | _ => ret mt (* TODO: throw "bad stack" error? *)
      end
    | bep evs1 evs2 =>
      match e with
      | sp e1 e2 =>
        res1 <- parallel_att_vm_thread evs1 e1 ;;
             res2 <- parallel_att_vm_thread evs2 e2 ;;
             ret (sp res1 res2)
      | _ => ret mt (* TODO: throw "bad stack" error? *)
      end
    end.

Fixpoint att_vm (is:list Instr) (e:Evidence) : COP Evidence :=
  foldM_COP vm_prim e is.
