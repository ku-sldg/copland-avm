Require Import GenStMonad MonadVM MonadAM ConcreteEvidence.
Require Import StAM VM_IO_Axioms Maps VmSemantics Event_system Term_system.

Require Import Coq.Arith.Peano_dec.


Require Import List.
Import ListNotations.

Check map_get.

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args, evidenceEvent (umeas n p i args)
| sev: forall n p, evidenceEvent (sign n p)
| hev: forall n p, evidenceEvent (hash n p).

Definition ioEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  let es := ev_sys t p in
  ev_in ev es /\ evidenceEvent ev.

Definition am_get_app_asp (p:Plc) (i:ASP_ID) : AM ASP_ID :=
  m <- gets st_aspmap ;;
  let maybeId := map_get m (p,i) in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

Fixpoint gen_appraisal_term (et:Evidence) : AM Term :=
  match et with
  | mt => ret (asp CPY)
  | uu i_t p e'_t =>
    app_id <- am_get_app_asp p i_t ;;
    let t1 := (asp (ASPC app_id [])) in
    t2 <- gen_appraisal_term e'_t ;;
    ret (bpar (NONE,NONE) t1 t2)
  | ss e1 e2 =>
    t1 <- gen_appraisal_term e1 ;;
    t2 <- gen_appraisal_term e2 ;;
    ret (bpar (NONE,NONE) t1 t2)
  | _ => ret (asp CPY)
  end.

Definition at1 := (asp (ASPC 1 [])).
Definition at2 := (asp (ASPC 2 [])).
Definition aterm := bseq (NONE,NONE) at1 at2.

Definition aet := eval aterm 0 mt.
Print aet.
Compute aet.

Definition acomp := (gen_appraisal_term aet).

Check runSt.

Definition ast :=
  mkAM_St [] 0 [((0,1),33); ((0,2),44)].

Definition appterm := (runSt ast acomp).
Compute appterm.
(*
     = (Some
          (bpar (NONE, NONE) (bpar (NONE, NONE) (asp (ASPC 3 [])) (asp CPY))
             (bpar (NONE, NONE) (asp (ASPC 4 [])) (asp CPY))),
       {| am_nonceMap := []; am_nonceId := 0; st_aspmap := [(0, 1, 3); (0, 2, 4)] |})
     : option Term * AM_St
*)

Compute aet.
(*
     = ss (uu 1 0 mt) (uu 2 0 mt)
     : Evidence
 *)
Definition evc := (run_vm (annotated aterm) empty_vmst).
Compute evc.

Fixpoint moveEv (e:EvidenceC) : (EvidenceC * BS) :=
  match e with
  | mtc => (mtc, 0)
  | uuc i bs e' => (e',bs)
  | ggc bs e' => (e',bs)
  | hhc bs e' => (e',bs)
  | nnc n bs e' => (e',bs)
  | ssc mtc e2 => moveEv e2
  | ssc e1 e2 => let (e1',bs) := moveEv e1 in
                ((ssc e1' e2),bs)
  | ppc e1 e2 => let (e1',bs) := moveEv e1 in
                ((ppc e1' e2),bs)
  end.

Compute (moveEv (st_ev evc)).
    

Definition getBS : VM BS :=
  e <- gets st_ev ;;
  let (e',bs) := moveEv e in
  put_ev e' ;;
  ret bs.
  
Definition do_prim_app (x:nat) (p:Plc) (a:ASP) : VM EvidenceC :=
  e <- gets st_ev ;;
  bs <- getBS ;;
  let args := [bs] in
  match a with
  | CPY => copyEv x p
  | ASPC asp_id _ =>
    invokeUSM x asp_id p args
  | SIG => signEv x p
  | HSH => hashEv x p
  end.

Fixpoint build_comp_app (t:AnnoTerm): VM unit :=
  match t with   
  | aasp (n,_) a =>
    p <- get_pl ;;
    e <- do_prim_app n p a ;;
    put_ev e
  | alseq r t1 t2 =>
    build_comp_app t1 ;;
    build_comp_app t2
  | abpar r _ t1 t2 =>
    build_comp_app t1 ;;
    build_comp_app t2
  | _ => ret tt
  end.

Definition fromOpt{A:Type} (o:option A) (a:A) : A :=
  match o with
  | Some t => t
  | None => a
  end.

Definition app_term := fromOpt (fst appterm) (asp CPY).
Compute app_term.

Definition app_term' :=
  (bpar (NONE, NONE) (asp (ASPC 44 [])) (asp CPY)).

Definition app_term'' :=
  (bpar (NONE, NONE) (asp (ASPC 33 [])) (asp (ASPC 44 [])) ).


Definition app_comp := (build_comp_app (annotated (app_term))).

Compute (st_ev evc).

Definition newst := mk_st (st_ev evc) [] 0 [].

Compute (runSt newst app_comp).
  

Fixpoint build_comp (t:AnnoTerm): VM unit :=
  match t with
    
  | aasp (n,_) a =>
    p <- get_pl ;;
    e <- do_prim n p a ;;
    put_ev e
  | aatt (reqi,rpyi) q t' =>
    sendReq reqi q t' ;;
    e <- get_ev ;;
    doRemote t' q e rpyi ;;
    e' <- receiveResp rpyi q ;;
    put_ev e'
  | alseq r t1 t2 =>
    build_comp t1 ;;
    build_comp t2 (* TODO: does evidence work out ok? *)
  | abseq (x,y) (sp1,sp2) t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_evm x sp1 sp2 e p ;;
    let '(e1,e2) := pr in
    put_ev e1 ;;
    build_comp t1 ;;
    e1r <- get_ev ;;
    put_ev e2 ;;
    build_comp t2 ;;
    e2r <- get_ev ;;
    put_ev (ssc e1r e2r) ;;
    add_tracem [Term.join (Nat.pred y) p]
        
(*

  | abseq (x,y) (sp1,sp2) t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_evm x sp1 sp2 e p ;;
    let '(e1,e2) := pr in
    put_ev e1 ;;
    push_stackm e2 ;;
    build_comp t1 ;;
    e <- get_ev ;;
    er <- pop_stackm ;; (* TODO:  is stack still necessary? *)
    put_ev er ;;
    push_stackm e ;;
    build_comp t2 ;;
    er' <- pop_stackm ;;
    er'' <- get_ev ;;
    put_ev (ssc er' er'') ;;
    add_tracem [Term.join (Nat.pred y) p]
*)
  | abpar (x,y) (sp1,sp2) t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_evm x sp1 sp2 e p ;;
    let '(e1,e2) := pr in
    let res1 := parallel_att_vm_thread t1 e in
    (* TODO: change this to a monadic function that consults an environment that is aware of the presence (or absence) of parallel avm threads.  Put initial evidence in store, let environment run the parallel thread and place result evidence, then query for result evidence here. *)
    let res2 := parallel_att_vm_thread t2 e2 in
    let el1 := parallel_vm_events t1 p in
    let el2 := parallel_vm_events t2 p in
    let loc1 := fst (range t1) in
    let loc2 := fst (range t2) in
    put_store loc1 res1 ;;
    put_store loc2 res2 ;;
    add_tracem (shuffled_events el1 el2) ;;
    e1r <- get_store_at loc1 ;;
    e2r <- get_store_at loc2 ;;
    put_ev (ppc e1r e2r) ;;
    add_tracem [Term.join (Nat.pred y) p]
  end.
