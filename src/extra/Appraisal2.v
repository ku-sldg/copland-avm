Require Import GenStMonad MonadVM MonadAM ConcreteEvidence.
Require Import StAM VM_IO_Axioms Maps VmSemantics Event_system Term_system.

Require Import Coq.Arith.Peano_dec.


Require Import List.
Import ListNotations.

Check map_get.

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args, evidenceEvent (umeas n p i args)
(*| sev: forall n p, evidenceEvent (sign n p)
| hev: forall n p, evidenceEvent (hash n p)*) .

Definition ioEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  let es := ev_sys t p in
  ev_in ev es /\ evidenceEvent ev.

Check bound_to.

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p q i i' n m args nmap nid amap,
    bound_to amap (p,i) i' ->
    appEvent (umeas n p i args) (mkAM_St nmap nid amap) (umeas m q i' (args ++ [n])).

Definition am_get_app_asp (p:Plc) (i:ASP_ID) : AM ASP_ID :=
  m <- gets st_aspmap ;;
  let maybeId := map_get m (p,i) in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

Fixpoint gen_appraisal_term (e:EvidenceC) (et:Evidence) : AM Term :=
  match e with
  | mtc =>
    match et with
    | mt => ret (asp CPY)
    | _ => failm
    end
  | uuc i bs e' =>
    match et with 
    | uu i_t args_t p e'_t =>
      app_id <- am_get_app_asp p i_t ;;
      t2 <- gen_appraisal_term e' e'_t ;;
      let t1 := (asp (ASPC app_id (args_t ++ [bs]))) in
      let res := (bseq (NONE,NONE) t1 t2) in
                     ret res
    | _ => failm
    end
  | ssc e1 e2 =>
    match et with
    | ss e1_t e2_t => 
      t1' <- (gen_appraisal_term e1 e1_t) ;;
          t2' <- (gen_appraisal_term e2 e2_t) ;;
          let res := (bseq (NONE,NONE) t1' t2') in (* BRP (NONE,NONE) t1' t2' *)
          ret res
    | _ => failm
    end
  | _ => ret (asp CPY)
  end.
    
      (*
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
    | ss e1_t e2_t => 
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
       
  | _ => ret (asp CPY)
end.
*)

Definition at1 := (asp (ASPC 1 [])).
Definition at2 := (asp (ASPC 2 [])).
Definition aterm := bseq (NONE,NONE) at1 at2.

Definition aet := eval aterm 0 mt.
Print aet.
Compute aet.

Definition evc_st := (run_vm (annotated aterm) empty_vmst).
Compute evc_st.
Definition evc := st_ev evc_st.
Compute evc.

Definition acomp := (gen_appraisal_term evc aet).
Compute acomp.

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
Definition evc_res := (run_vm (annotated aterm) empty_vmst).
Compute evc.

Definition fromOpt{A:Type} (o:option A) (a:A) : A :=
  match o with
  | Some t => t
  | None => a
  end.

Definition app_term := fromOpt (fst appterm) (asp CPY).
Compute app_term.

(*

Definition app_term' :=
  (bpar (NONE, NONE) (asp (ASPC 44 [])) (asp CPY)).

Definition app_term'' :=
  (bpar (NONE, NONE) (asp (ASPC 33 [])) (asp (ASPC 44 [])) ).
*)


Definition app_comp := (build_comp (annotated (app_term))).

Definition app_comp_res := runSt empty_vmst app_comp.
Compute app_comp_res.
Definition tr_app_comp := st_trace (snd app_comp_res).
Compute tr_app_comp.

Check In.

Require Import StructTactics.

Definition allMapped (t:AnnoTerm) (p:Plc) (st: AM_St) : Prop :=
  forall t st aspmap n q i l ,
    ioEvent t p (umeas n q i l) ->
    aspmap = st_aspmap st ->
    exists j,
      bound_to aspmap (q,i) j.

Set Nested Proofs Allowed.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Lemma app_correct :
  forall aterm ev ast aet evc acomp appterm app_term
    app_comp app_comp_res tr_app_comp ,
  aet = eval aterm 0 mt ->
  evc = st_ev (run_vm (annotated aterm) empty_vmst) ->
  acomp = (gen_appraisal_term evc aet) ->
  appterm = (runSt ast acomp) ->
  app_term = fromOpt (fst appterm) (asp CPY) ->
  app_comp = (build_comp (annotated app_term)) ->
  app_comp_res = runSt empty_vmst app_comp ->
  tr_app_comp = st_trace (snd app_comp_res) ->
                       
  ioEvent (annotated aterm) 0 ev ->
  allMapped (annotated aterm) 0 ast ->
  exists ev', In ev' tr_app_comp /\ appEvent ev ast ev'.
Proof.
  induction aterm0; intros; subst.
  -
    destruct a.
    +
      invc H7.
      invc H.
      invc H0.
    +
      inv H7.
      inv H.
      repeat find_inversion.
     
      simpl.
      monad_unfold.
      unfold allMapped in *.
      edestruct H8 with (st:=ast0).
      apply H7.
      reflexivity.
      unfold am_get_app_asp.
      monad_unfold.
      simpl.
      unfold runSt.
      simpl in *.
      repeat break_let.
      simpl in *.
      inv H1.
      rewrite H2 in *.
      invc Heqp0.
      invc Heqp.
      simpl.
      eexists.
      split.
      right. left. eauto.
      destruct a.
      econstructor.
      simpl in *.
      assumption.
    + invc H7.
      invc H.
      invc H0.
    + invc H7.
      invc H.
      invc H0.
  -
    inv H7.
    Print ioEvent.
    inv H0.
    monad_unfold.
    destruct empty_vmst.
    simpl in *.
    monad_unfold.
    unfold runSt.
    monad_unfold.

    edestruct IHaterm0; eauto.
    econstructor.
    Lemma hfhf : forall x n t p,
      ev_in x (ev_sys (annotated (att n t)) p) ->
      ev_in x (ev_sys (annotated t) p).
    Proof.
    Admitted.
    eapply hfhf; eauto.
    econstructor.

    (*
    Lemma jfjf : forall n p t st,
      allMapped (annotated (att n t)) p st ->
      allMapped (annotated t) p st.
    Proof.
    Admitted.

    eapply jfjf; eauto. *)
    destruct_conjs.
    inv H2.

    exists (umeas m q i' (args ++ [n0])).
    split.
    unfold runSt in *.

    Lemma jhjh : forall x t p n t_st init_st init_st',
       In x
         (StVM.st_trace
            (snd
               (build_comp
                  (annotated
                     (fromOpt
                        (fst
                           (gen_appraisal_term
                              (StVM.st_ev
                                 (run_vm (annotated t)
                                    t_st))
                              (eval t p mt)
                              init_st)) 
                        (asp CPY)))
                  init_st'))) ->
       In x
         (StVM.st_trace
            (snd
               (build_comp
                  (annotated
                     (fromOpt
                        (fst
                           (gen_appraisal_term
                              (StVM.st_ev
                                 (run_vm (annotated (att n t))
                                    t_st))
                              (eval t n mt)
                              init_st)) 
                        (asp CPY)))
                  init_st'))).
    Proof.
    Admitted.

    eapply jhjh; eauto.
    eauto.
  - inv H7.
    inv H0.
    edestruct IHaterm0_1; eauto.
    admit.

Lemma app_correct : forall ev,
    ioEvent (annotated aterm) 0 ev ->
    exists ev', In ev' tr_app_comp /\
           appEvent ev ast ev'.
Proof.
  intros.
  cbv in *.
  invc H.
  invc H0.
  invc H3.
  inv H1.
  invc H3.
  invc H2.
  invc H3.
  invc H1.
  eexists.
  split.
  right. right. left. eauto.
  econstructor.
  econstructor. simpl. tauto.
  invc H3. invc H1.
  eexists.
  split.
  right. right. right. right. right. right. left. eauto.
  econstructor.
  econstructor. simpl. tauto.
  invc H2. invc H1.
Defined.
  
  
  

