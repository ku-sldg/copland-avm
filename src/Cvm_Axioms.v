Require Import IO_Stubs ResultT Cvm_Monad Attestation_Session Cvm_Impl.

Axiom parallel_vm_thread_res_axiom : forall i t e e' p,
  parallel_vm_thread i p e t = resultC e' ->
  forall st sc,
    st = {| st_ev := e; st_trace := nil; st_evid := i; st_config := sc |} ->
    session_plc sc = p ->
    exists st' u,
      build_cvm t st = (resultC u, st') /\ st_ev st' = e'.

Axiom parallel_vm_thread_err_axiom : forall i t e p err,
  parallel_vm_thread i p e t = errC err ->
  forall st sc,
    st = {| st_ev := e; st_trace := nil; st_evid := i; st_config := sc |} ->
    session_plc sc = p ->
    exists st',
      build_cvm t st = (errC err, st').

Axiom do_remote_res_axiom : forall sc p e t e',
  do_remote sc p e t = resultC e' ->
  forall st sc' i,
    (* NOTE: This is maybe a bit stronger than we want!
    we really need to be looking at the NEW session config that was
    created via the passed session *)
    st = {| st_ev := e; st_trace := nil; st_evid := i; st_config := sc' |} ->
    exists st' u,
      build_cvm t st = (resultC u, st') /\ st_ev st' = e' /\
      session_plc sc' = p /\
      session_context sc' = session_context sc.

Axiom do_remote_err_axiom : forall sc p e t s,
  do_remote sc p e t = errC s ->
  forall st sc' i,
    (* NOTE: This is maybe a bit stronger than we want!
    we really need to be looking at the NEW session config that was
    created via the passed session *)
    st = {| st_ev := e; st_trace := nil; st_evid := i; st_config := sc' |} ->
    exists st',
      build_cvm t st = (errC (dispatch_error s), st').
