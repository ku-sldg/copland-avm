Require Import ConcreteEvidence GenStMonad.
Require Import Maps (*OptMonad*) MonadAM  StructTact.StructTactics.

Require Import List.
Import ListNotations.

(*
Inductive App_Instr: Set :=
| asp_app: ASP_ID -> BS -> App_Instr
| g_app: Plc -> BS -> EvidenceC -> App_Instr
| h_app: BS -> EvidenceC -> App_Instr
| n_app: N_ID -> BS -> App_Instr.

Fixpoint app_compile (e:EvidenceC) : list App_Instr :=
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
Definition encode_ev : EvidenceC -> BS. Admitted.
(* params: encoded payload -> private key -> signature *)
Definition check_sig : BS -> Pri_Key -> BS -> bool. Admitted.

Definition check_ev_sig (e:EvidenceC) (k:Pri_Key) (sig:BS) : bool :=
  let payload := encode_ev e in
  check_sig payload k sig.

(*
Definition check_ev_pl (e:EvidenceC) (p:Plc) (sig:BS) : option bool :=
  k <- map_get pri_keys p ;; 
    ret (check_ev_sig e k sig). *)

(* params: payload -> hash *)
(* TODO: incorporate hash algorithm choice (policy) here? *)
Definition check_hash : BS -> BS -> bool. Admitted.

Definition check_ev_hash (e:EvidenceC) (bs:BS) : bool :=
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

Fixpoint appraise (e:EvidenceC) : option bool :=
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
Definition sig_map := Map Plc ASP_ID.
Definition hsh_map := Map Plc ASP_ID.
Definition asp_map := Map (Plc * ASP_ID) ASP_ID.
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

Fixpoint gen_appraisal_term (e:EvidenceC) (et:Evidence) : APP Term :=
  match e with
  | mtc =>
    match et with
    | mt => ret (asp CPY)
    | _ => failm
    end
  | uuc i bs e' =>
    match et with 
    | uu i_t p e'_t =>
      let app_id := 0 in (* app_id <- am_get_asp_asp p i_t *)
      t2 <- gen_appraisal_term e' e'_t ;;
      let t1 := (asp (ASPC app_id)) in
      let res := (bpar (NONE,NONE) t1 t2) in
                     ret res
    | _ => failm
    end
  | 
  | _ => failm
  end.
    












(*
Definition helper_gen_app (a:ASP) (p:Plc) (e:EvidenceC) : APP (Term * EvidenceC) :=
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
    
               
  

Fixpoint gen_appraisal_term' (t:Term) (p:Plc) (e:EvidenceC) : APP (Term * EvidenceC) :=
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
      |_ => failm (* error "evidence mismath on BRS-SS" *)
      end
  | bpar _ t1 t2 =>
      match e with
      | ppc e1 e2 =>   
        (* (t1',_) *) v1 <- (gen_appraisal_term' t1 p e1) ;;
        (* (t2',_) *) v2 <- (gen_appraisal_term' t2 p e2) ;;
        ret ((bpar (NONE,NONE) (fst v1) (fst v2)),mtc)
      |_ => failm (* error "evidence mismath on BRP-PP" *)
      end
  end.

*)

Require Import Instr MonadVM VmSemantics.

Lemma run_vm_good_ev : forall t tr tr' e e' s s' p p' o o',
  run_vm (instr_compiler t)
         {| st_ev := e; st_stack := s;  st_trace := tr; st_pl := p; st_store := o |} =
  {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := o' |} ->
  EvcT (unanno t) e e'.
Proof.
Admitted.



    

Theorem someEv : forall t tr tr' e e' s s' p p' o o' app_st,
  run_vm (instr_compiler t)
         {| st_ev := e; st_stack := s;  st_trace := tr; st_pl := p; st_store := o |} =
  {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := o' |} ->
  exists app_st' v,
    runSt app_st (gen_appraisal_term' (unanno t) p e') = (Some v,app_st').
Proof.
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
    
  
  