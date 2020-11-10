Require Import MonadVM GenStMonad Term ConcreteEvidence Axioms_Io.

Require Import List.
Import ListNotations.

Fixpoint build_comp (t:AnnoTerm): VM unit :=
  match t with
  | aasp (n,_) a =>
    e <- do_prim n a ;;
    put_ev e
  | aatt (reqi,rpyi) q t' =>
    sendReq reqi q t' ;;
    e <- get_ev ;;
    doRemote t' q e rpyi ;;
    e' <- receiveResp rpyi q ;;
    put_ev e'
  | alseq r t1 t2 =>
    build_comp t1 ;;
    build_comp t2
(*  
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

  | abpar (x,y) (sp1,sp2) t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_evm x sp1 sp2 e p ;;
    let '(e1,e2) := pr in
    (*
    let res1 := parallel_att_vm_thread t1 e in
    (* TODO: change this to a monadic function that consults an environment that is aware of the presence (or absence) of parallel avm threads.  Put initial evidence in store, let environment run the parallel thread and place result evidence, then query for result evidence here. *)
    let res2 := parallel_att_vm_thread t2 e2 in
    let el1 := parallel_vm_events t1 p in
    let el2 := parallel_vm_events t2 p in
    let loc1 := fst (range t1) in
    let loc2 := fst (range t2) in
    put_store loc1 res1 ;;
    put_store loc2 res2 ;;
    add_tracem (shuffled_events el1 el2) ;; *)

    runParThreads t1 t2 p e1 e2 ;;
    let loc1 := fst (range t1) in
    let loc2 := fst (range t2) in
       
    e1r <- get_store_at loc1 ;;
    e2r <- get_store_at loc2 ;;
    put_ev (ppc e1r e2r) ;;
    add_tracem [Term.join (Nat.pred y) p]
*)
  end.

(** Function-style semantics for VM *)

Definition run_vm (t:AnnoTerm) st : vm_st :=
  execSt st (build_comp t).


Axiom build_comp_external' : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr:list Ev),
    build_comp t {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := remote_evidence t e;
        st_trace := tr ++ (remote_trace t n);
        st_pl :=
          st_pl
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
        st_store :=
          st_store
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
     |}).
