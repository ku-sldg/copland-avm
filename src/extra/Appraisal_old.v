(*


Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidenceT GenStMonad.
Require Import Maps. (*OptMonad*) (* MonadAM *)  (*StructTact.StructTactics. *)

Require Import StructTactics.
Require Import List.
Import ListNotations.

Require Import Coq.Arith.EqNat.

(*
Inductive App_Instr: Set :=
| asp_app: ASP_ID -> BS -> App_Instr
| g_app: Plc -> BS -> EvidenceTC -> App_Instr
| h_app: BS -> EvidenceTC -> App_Instr
| n_app: N_ID -> BS -> App_Instr.

Fixpoint app_compile (e:EvidenceTC) : list App_Instr :=
  match e with
  | mtc => []
  | uuc i bs e' => [asp_app i bs] ++ (app_compile e')
  | ggc p bs e' => [g_app p bs e'] ++ (app_compile e')                   
  | hhc bs e' => [h_app bs e'] ++ (app_compile e')
  | nnc n_id bs e' => [n_app n_id bs] ++ (app_compile e')
  | ssc e1 e2 => (app_compile e1) ++ (app_compile e2)
  | ppc e1 e2 => (app_compile e1) ++ (app_compile e2)
  end.

Notation Pri_Key := nat (only parsing).

Definition pri_keys : Map Plc Pri_Key. Admitted.
Definition golden_measurements : Map ASP_ID BS. Admitted.
Definition nonce_map : Map N_ID BS. Admitted.

(* params: id -> golden -> actual *)
Definition check_measurement : ASP_ID -> BS -> BS -> bool. Admitted.
Definition encode_ev : EvidenceTC -> BS. Admitted.
(* params: encoded payload -> private key -> signature *)
Definition check_sig : BS -> Pri_Key -> BS -> bool. Admitted.

Definition check_ev_sig (e:EvidenceTC) (k:Pri_Key) (sig:BS) : bool :=
  let payload := encode_ev e in
  check_sig payload k sig.

(*
Definition check_ev_pl (e:EvidenceTC) (p:Plc) (sig:BS) : option bool :=
  k <- map_get pri_keys p ;; 
    ret (check_ev_sig e k sig). *)

(* params: payload -> hash *)
(* TODO: incorporate hash algorithm choice (policy) here? *)
Definition check_hash : BS -> BS -> bool. Admitted.

Definition check_ev_hash (e:EvidenceTC) (bs:BS) : bool :=
  let payload := encode_ev e in
  check_hash payload bs.

Check Nat.eqb.
*)

(*
Definition check_nonce (n : N_ID) (bs:BS) : option bool :=
  g_bs <- map_get nonce_map n ;;
       ret (Nat.eqb bs g_bs).   


Definition check_asp (x:ASP_ID) (m:BS) : option bool :=
  g_bs <- (map_get golden_measurements x) ;;
       ret (check_measurement x g_bs m).

Fixpoint appraise (e:EvidenceTC) : option bool :=
  match e with
  | mtc => Some true
  | uuc i bs e =>
    b <- check_asp i bs ;;
      res <- appraise e ;;
      ret (andb b res)
  | ggc p sig e =>
    b <- check_ev_pl e p sig ;;
      res <- appraise e ;;
          ret (andb b res)
  | hhc h e =>
    let b := check_ev_hash e h in
      res <- appraise e ;;
          ret (andb b res)
  | nnc n_id bs e =>
    b <- check_nonce n_id bs ;;
      res <- appraise e ;;
      ret (andb b res)
  | ssc e1 e2 =>
    res1 <- appraise e1 ;;
         res2 <- appraise e2 ;;
         ret (andb res1 res2)
  | ppc e1 e2 =>
    res1 <- appraise e1 ;;
         res2 <- appraise e2 ;;
         ret (andb res1 res2)
  end.

Definition appraiseI' (i:App_Instr): option bool :=
  match i with
  | asp_app x bs => check_asp x bs
  | g_app p bs e' => check_ev_pl e' p bs
  | h_app bs e' => Some (check_ev_hash e' bs)
  | n_app nid bs => check_nonce nid bs
  end.

Fixpoint appraiseI (o:option bool) (i:App_Instr): option bool :=
  b <- o ;;
    b' <- appraiseI' i ;;
    ret (andb b b').
    
Check fold_left.
Definition run_app (il:list App_Instr) : option bool :=
  fold_left appraiseI il (Some true).
    

Theorem app_eq_appI: forall e,
    let il := app_compile e in
    appraise e = run_app il.
Abort.



Require Import StVM Instr VmSemantics.

Definition mt_st := mk_st mtc [] [] 0 [].

Theorem can_app: forall t,
    let att_il := instr_compiler t in
    let ev_res := run_vm_t t mt_st in
    let app_il := app_compile (st_ev ev_res) in
    let optB := run_app app_il in
    exists b, optB = Some b.
Abort.
 *)




(* Specific APP monad state *)
Definition sig_map := MapC Plc ASP_ID.
Definition hsh_map := MapC Plc ASP_ID.
Definition asp_map := MapC (Plc * ASP_ID) ASP_ID.
Record app_st : Type := mk_app_st
                         {st_sigmap :sig_map;
                          st_hshmap :hsh_map; 
                          st_aspmap :asp_map;
                          st_nonceCheck_asp :ASP_ID}.

Definition empty_app_st := mk_app_st [] [] [] 0.
Check empty_app_st.


Definition APP := St app_st.

(*
Definition am_get_asp_asp (p:Plc) (i:ASP_ID) : APP ASP_ID :=
  m <- gets asp_map ;;
  let maybeId = M.lookup (p,i) m
  case maybeId of
   Just newI -> return newI
   Nothing -> error $ "appraisal asp for ASP_ID " ++ (show i) ++ " at place " ++ (show p) ++ " not registered."
*)

Fixpoint gen_appraisal_term (e:EvidenceTC) (et:EvidenceT) : APP Term :=
  match e with
  | mtc =>
    match et with
    | mt_evt=> ret (asp CPY)
    | _ => failm
    end
  | uuc i bs e' =>
    match et with 
    | asp_evt i_t p e'_t =>
      let app_id := 0 in (* app_id <- am_get_asp_asp p i_t *)
      t2 <- gen_appraisal_term e' e'_t ;;
      let t1 := (asp (ASPC app_id)) in
      let res := (bpar (NONE,NONE) t1 t2) in
                     ret res
    | _ => failm
    end
  | ggc bs e' =>
    match et with
    | gg p e'_t =>
        let sig_id := 42 in      (* sig_id <- am_get_sig_asp p *)
        (* let evBits = encodeEv e' --BL.toStrict (DA.encode e)
            evBitsArg = show evBits
            sigArg = show bs *)
        t2 <- gen_appraisal_term e' e'_t ;;
        let t1 := (asp (ASPC sig_id)) in   (* (ASP sig_id [evBitsArg,sigArg]) *)
        let res := (bpar (NONE,NONE) t1 t2) in   (* BRP (NONE,NONE) t1 t2 *)
        ret res
    | _ => failm
    end
  | hhc bs e' =>
    match et with
    | hh p e'_t =>
        let hsh_id := 0 in      (* hsh_id <- am_get_hsh_asp p *)
        (* let evBits = encodeEv e' --BL.toStrict (DA.encode e)
            evBitsArg = show evBits
            sigArg = show bs *)
        t2 <- gen_appraisal_term e' e'_t ;;
        let t1 := (asp (ASPC hsh_id)) in   (* (ASP sig_id [evBitsArg,sigArg]) *)
        let res := (bpar (NONE,NONE) t1 t2) in   (* BRP (NONE,NONE) t1 t2 *)
        ret res
    | _ => failm
    end
  | ssc e1 e2 =>
    match et with
    | split_evt e1_t e2_t => 
      t1' <- (gen_appraisal_term e1 e1_t) ;;
          t2' <- (gen_appraisal_term e2 e2_t) ;;
          let res := (bpar (NONE,NONE) t1' t2') in (* BRP (NONE,NONE) t1' t2' *)
          ret res
    | _ => failm
    end
  | ppc e1 e2 =>
    match et with
    | pp e1_t e2_t => 
      t1' <- (gen_appraisal_term e1 e1_t) ;;
          t2' <- (gen_appraisal_term e2 e2_t) ;;
          let res := (bpar (NONE,NONE) t1' t2') in (* BRP (NONE,NONE) t1' t2' *)
          ret res
    | _ => failm
    end      
  | nnc _ _ _ =>  ret (asp CPY) (* Dummy nonce case for now.  TODO: robustify *)
  end.
    












(*
Definition helper_gen_app (a:ASP) (p:Plc) (e:EvidenceTC) : APP (Term * EvidenceTC) :=
  match a with
  | CPY => ret (asp CPY,e)
  | ASPC i =>
    match e with
    | uuc _ bs e' => ret (asp (ASPC 0),e')
    | _ => failm
    end
  | SIG =>
    match e with
    | ggc _ _ e' => ret (asp (ASPC 0),e')
    | _ => failm
    end
  | HSH =>
    match e with
    | hhc _ e' => ret (asp (ASPC 0),e')
    | _ => failm
    end
  end.
    
               
  

Fixpoint gen_appraisal_term' (t:Term) (p:Plc) (e:EvidenceTC) : APP (Term * EvidenceTC) :=
  match t with
  | asp a => helper_gen_app a p e
  | att q t' => gen_appraisal_term' t' q e
  | lseq t1 t2 =>
   (* (t2', e2) *)v2 <- (gen_appraisal_term' t2 p e) ;;
             (* (t1',e1) *) v1 <- (gen_appraisal_term' t1 p (snd v2)) ;;
                     ret ((bpar (NONE,NONE) (fst v1) (fst v2)),(snd v1))
  | bseq _ t1 t2 =>
      match e with
      | ssc e1 e2 =>   
        (* (t1',_) *) v1 <- (gen_appraisal_term' t1 p e1) ;;
        (* (t2',_) *) v2 <- (gen_appraisal_term' t2 p e2) ;;
        ret ((bpar (NONE,NONE) (fst v1) (fst v2)),mtc)
      |_ => failm (* error "EvidenceT mismath on BRS-SS" *)
      end
  | bpar _ t1 t2 =>
      match e with
      | ppc e1 e2 =>   
        (* (t1',_) *) v1 <- (gen_appraisal_term' t1 p e1) ;;
        (* (t2',_) *) v2 <- (gen_appraisal_term' t2 p e2) ;;
        ret ((bpar (NONE,NONE) (fst v1) (fst v2)),mtc)
      |_ => failm (* error "EvidenceT mismath on BRP-PP" *)
      end
  end.

*)

Require Import MonadVM VmSemantics.

(*
Lemma run_vm_good_ev : forall t tr tr' e e' s s' p p' o o',
  run_vm (instr_compiler t)
         {| st_ev := e;
            st_stack := s;
            st_trace := tr;
            st_pl := p;
            st_store := o |} =
  {| st_ev := e';
     st_stack := s';
     st_trace := tr';
     st_pl := p';
     st_store := o' |} ->
  EvcT (unanno t) e e'.
Proof.
Admitted.
*)


Set Nested Proofs Allowed.




(*
Lemma EvcT_iff_eval : forall annt e e',
    eval annt e = e' <-> EvcT annt e e'.
Admitted.
*)

Require Import Coq.Program.Tactics.

Definition aterm := lseq (asp (ASPC 1)) (asp SIG).

Print anno.

Definition aev := (run_vm (annotated aterm)
                          {| st_ev := mtc;
                             st_trace := [];
                             st_pl := 0;
                             st_store := [] |}).
Compute (st_ev aev).
Print signEv.

Compute (gen_appraisal_term (st_ev aev) (gg 0 (asp_evt 1 0 mt_evt))).

Theorem someEv_if_well_formed : forall e' app_st e't,
  Ev_Shape e' e't -> 
  exists app_st' v,
    runSt app_st (gen_appraisal_term e' e't) = (Some v,app_st').
Proof.
  intros.
  generalize dependent app_st0.
  induction H; intros;
    try (simpl; eexists; eexists; reflexivity).
  - simpl.
    edestruct IHEv_Shape.
    destruct_conjs.
    eexists; eexists.
    simpl.
    monad_unfold.
    unfold runSt in *.
    rewrite H1.
    reflexivity.
  - simpl.
    edestruct IHEv_Shape.
    destruct_conjs.
    eexists; eexists.
    monad_unfold.
    unfold runSt in *.
    rewrite H1.
    reflexivity.
  - simpl.
    edestruct IHEv_Shape.
    destruct_conjs.
    eexists; eexists.
    monad_unfold.
    unfold runSt in *.
    rewrite H1.
    reflexivity.
  - simpl.
    edestruct IHEv_Shape1.
    edestruct IHEv_Shape2.
    destruct_conjs.
    eexists; eexists.
    monad_unfold.
    unfold runSt in *.
    rewrite H4.
    rewrite H3.
    reflexivity.
  - simpl.
    edestruct IHEv_Shape1.
    edestruct IHEv_Shape2.
    destruct_conjs.
    eexists; eexists.
    monad_unfold.
    unfold runSt in *.
    rewrite H4.
    rewrite H3.
    reflexivity.
Defined.


(* 
Lemma eval_iff_evalR: forall t p e e',
    evalR t p e e' <-> eval t p e = e'.
 *)

(*
Lemma multi_ev_eval : forall t tr tr' e e' s s' p p' o o',
    run_vm (instr_compiler t)
           {| st_ev := e; st_stack := s;  st_trace := tr; st_pl := p; st_store := o |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := o' |}  ->
    e' = eval (unanno t) e.
 *)

(*
Theorem someEv_if_well_formed : forall e' app_st e't,
  Ev_Shape e' e't -> 
  exists app_st' v,
    runSt app_st (gen_appraisal_term e' e't) = (Some v,app_st').
 *)

Axiom para_eval_thread: forall e annt,
    parallel_eval_thread annt e = eval annt e.

Lemma evShape_eval: forall e et p annt,
    Ev_Shape e et ->
    Ev_Shape (eval annt e) (Term.eval annt p et).
Proof.
  intros.
  generalize dependent p.
  generalize dependent e.
  generalize dependent et.
  induction annt; intros.
  - simpl.
    destruct a; simpl; eauto.
  - simpl.
    rewrite <- remote_eval.
    eauto.
  - simpl.
    eauto.
  - destruct s.
    destruct s; destruct s0; simpl; eauto.
  - destruct s.
    destruct s; destruct s0; simpl;
    repeat rewrite para_eval_thread in *;
    eauto.
Defined.


Lemma someEv' : forall t tr tr' e e' p p' o o' et,
  run_vm (t)
         {| st_ev := e;
            st_trace := tr;
            st_pl := p;
            st_store := o |} =
  {| st_ev := e';
     st_trace := tr';
     st_pl := p';
     st_store := o' |} ->

  Ev_Shape e et ->
  Ev_Shape e' (Term.eval (unanno t) p et).
Proof.
  intros.
  assert (Term.evalR (unanno t) p et (Term.eval (unanno t) p et)).
  {
    rewrite Term.eval_iff_evalR. reflexivity.
  }
  assert (e' = eval (unanno t) e) as hi.
  {
    eapply multi_ev_eval; eauto.
  }
  rewrite hi.
  eapply evShape_eval; eauto.
Defined.


Theorem someEv : forall t tr tr' e e' p p' o o' app_st et,
  run_vm (t)
         {| st_ev := e;
            st_trace := tr;
            st_pl := p;
            st_store := o |} =
  {| st_ev := e';
     st_trace := tr';
     st_pl := p';
     st_store := o' |} ->

 Ev_Shape e et ->
 (* evalR (unanno t) p et e't -> (* e't = Term.eval (unanno t) p mt_evt-> *) *)
  exists app_st' v,
    runSt app_st (gen_appraisal_term e' (Term.eval (unanno t) p et)) = (Some v,app_st').
Proof.
  intros.
  assert (Ev_Shape e' (Term.eval (unanno t) p et)).
  eapply someEv'; eauto.
  eapply someEv_if_well_formed; eauto.
Qed.

  














  
    
    
    
    
(*    
    

Theorem someEv : forall t tr tr' e e' et s s' p p' o o' app_st e't,
  run_vm (instr_compiler t)
         {| st_ev := e;
            st_stack := s;
            st_trace := tr;
            st_pl := p;
            st_store := o |} =
  {| st_ev := e';
     st_stack := s';
     st_trace := tr';
     st_pl := p';
     st_store := o' |} ->

  ET e et ->
  evalR (unanno t) p et e't -> (* e't = Term.eval (unanno t) p mt_evt-> *)
  exists app_st' v,
    runSt app_st (gen_appraisal_term e' e't) = (Some v,app_st').
Proof.
  intros.
 (* assert (EvcT (unanno t) mtc e').
  eapply run_vm_good_ev; eauto. *)
  generalize dependent p.
  generalize dependent e'.
  generalize dependent tr.
  generalize dependent tr'.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent p'.
  generalize dependent app_st0.
  generalize dependent e't.
  generalize dependent e.
  generalize dependent et.
  induction t; intros.
  - 

    (*
    assert (EvcT  (unanno (aasp r a)) e e').
    eapply run_vm_good_ev; eauto. *)

    destruct a; simpl;
      try (invc H1; invc H;
           eapply wf_gen; (try econstructor); eauto).
  -
    (*
     assert (EvcT (unanno (aatt r n t)) e e').
     eapply run_vm_good_ev; eauto. *)

    invc H1.
    eapply IHt.
    eassumption.

    simpl in H.
    monad_unfold.
    unfold run_vm_step in H. monad_unfold.


    rewrite run_at.


    assert (eval (unanno t) e = e').
    { erewrite remote_eval.
      invc H.
      destruct r.
      simpl in *.
      unfold run_vm_step in *. monad_unfold.
      invc H2.
      reflexivity. }

    rewrite H1.
    reflexivity.
    eassumption.
  -
    invc H1.

    edestruct destruct_compiled_appended.
    eassumption. clear H.
    destruct_conjs.
    fold instr_compiler in *.

    assert (H1 = eval (unanno t1) e) as hi.
    {
      admit.
    }    
    rewrite hi in *. clear hi.

    (* assert (e'1 = eval (unanno t1) mtc). admit.
    rewrite <- H13 in H6. *)

    (*
    edestruct IHt1.
    eassumption.
    eassumption.
    eassumption.
    destruct_conjs. *)

    eapply IHt2.
    assert (ET (eval (unanno t1) e) e'0) as hi.
    { 
      admit.
    }
    
    apply hi.
    eassumption.
    assert (p = H2) as hi.
    {
      admit.
    }
    
    rewrite <- hi.
    eassumption.
  -
    
    


    apply H10.



    
    apply H6.
    eassumption.

    eapply IHt2.
    
                                        
    

    
    eassumption.
    simpl in H6.
    
    
      
    reflexivity.

    
    invc H5
    
    
  
  

























  intros.
  assert (EvcT (unanno t) e e').
  eapply run_vm_good_ev; eauto.
  generalize dependent p.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent tr.
  generalize dependent tr'.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent p'.
  induction t; intros.
  - unfold unanno in *.
    destruct a; simpl; eexists; eexists;
      try (invc H0; reflexivity).
  - Print unanno.
    simpl.
    eapply IHt.
    simpl in H0.
    invc H0.
    eassumption.
    admit.
  - simpl.
    invc H0.
    monad_unfold.

    edestruct destruct_compiled_appended.
    eassumption.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.

    destruct H1. destruct H1.
     assert (EvcT (unanno t2) x0 e'). {
       eapply run_vm_good_ev. eauto. }

     edestruct IHt2.
     apply H4.
     apply H1.
     destruct H5.
     assert (p = x2). admit.
     rewrite H7.
     rewrite H5.


    
    assert (EvcT (unanno t1) e x0). {
      eapply run_vm_good_ev; eauto. }

    edestruct IHt1.
    apply H8.
    eassumption.

    destruct H9.
    destruct x6.
    destruct x8.
    simpl.
    rewrite <- H7.

    assert (x0 = e0). admit. (* Interesting symmetry:  t1(e) = x0, gen_app_term t2(e') = e0 *)
    assert (app_st0 = x5). admit. (* TODO: st immutable *)

    rewrite <- H10.
    rewrite <- H11.
    rewrite H9.
    eexists. eexists. reflexivity.
  - simpl.
    invc H0.
    monad_unfold.

    unfold run_vm_step in H.
    simpl in H.
    monad_unfold.
    
    edestruct destruct_compiled_appended.
    eassumption.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.

    destruct H1. destruct H1.

    do_run.
    monad_unfold.
    simpl in H4.
    monad_unfold.
    unfold pop_stackm in H4.
    monad_unfold.
    simpl in H4.

    edestruct destruct_compiled_appended.
    eapply H4.



    
     assert (EvcT (unanno t2) x0 e'). {
       eapply run_vm_good_ev; eauto. }

     edestruct IHt2.
     apply H7.
     apply H1.
     destruct H8.
     destruct H4.

      
      


      }
    eassumption.
    admit.
    
  
  *)
