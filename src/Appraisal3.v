Require Import GenStMonad MonadVM MonadAM ConcreteEvidence.
Require Import StAM VM_IO_Axioms Maps VmSemantics Event_system Term_system.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


(*
Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args, evidenceEvent (umeas n p i args)
(*| sev: forall n p, evidenceEvent (sign n p)
| hev: forall n p, evidenceEvent (hash n p)*) .

(*
Definition measEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  let es := ev_sys t p in
  ev_in ev es /\ evidenceEvent ev.
 *)

Definition measEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  events t p ev /\ evidenceEvent ev.

Check bound_to.

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p q i i' n m args nmap nid amap,
    bound_to amap (p,i) i' ->
    appEvent (umeas n p i args) (mkAM_St nmap nid amap) (umeas m q i' (args ++ [n])).
*)

Definition am_get_app_asp (p:Plc) (i:ASP_ID) : AM ASP_ID :=
  m <- gets st_aspmap ;;
  let maybeId := map_get m (p,i) in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

Fixpoint gen_appraisal_comp (e:EvidenceC) (et:Evidence) : AM (VM unit) :=
  match e with
  | mtc =>
    match et with
    | mt => ret (ret tt)
    | _ => failm
    end   
  | uuc i bs e' =>
    match et with 
    | uu i_t args_t p e'_t =>
      app_id <- am_get_app_asp p i_t ;;
      let c1 :=
          e <- invokeUSM 0 app_id p (args_t ++ [bs]) ;;  (* TODO: is bogus event id ok here? *)
          put_ev e in
      c2 <- gen_appraisal_comp e' e'_t ;;
      ret (c1 ;; c2)
    | _ => failm
    end
  | ggc bs e' =>
    match et with
    | gg p e'_t =>
      ret (ret tt)
    | _ => failm
    end
  | hhc bs e' =>
    match et with
    | hh p e'_t =>
      ret (ret tt)
    | _ => failm
    end
  | nnc nid bs e' =>
    match et with
    | nn nid_t e'_t =>
      ret (ret tt)
    | _ => failm
    end
  | ssc e1 e2 =>
    match et with
    | ss e1_t e2_t => 
      c1 <- gen_appraisal_comp e1 e1_t ;;
          c2 <- gen_appraisal_comp e2 e2_t ;;
          ret (c1 ;; c2)
    | _ => failm
    end
  | ppc e1 e2 =>
    match et with
    | pp e1_t e2_t => 
      c1 <- gen_appraisal_comp e1 e1_t ;;
          c2 <- gen_appraisal_comp e2 e2_t ;;
          ret (c1 ;; c2)
    | _ => failm
    end
  end.

Check build_comp.
Check runSt.
Check run_vm.
Check eval.

(*
Definition run_vm_fresh (t:AnnoTerm) :=
  run_vm t empty_vmst.
Check run_vm_fresh.


Definition run_vm_fresh_t (t:Term) :=
  run_vm (annotated t) empty_vmst.
Check run_vm_fresh_t.
*)

Definition build_app_comp (t: AnnoTerm) (p:Plc) (st:vm_st) : AM (VM unit) :=
  let vm_res_st := run_vm t st in
  let evc := st_ev vm_res_st in
  let evt := eval (unanno t) p mt in
  app_comp <- gen_appraisal_comp evc evt ;;
  ret (app_comp).

Definition build_app_comp_t (t:Term) (p:Plc) (st:vm_st) : AM (VM unit) :=
  build_app_comp (annotated t) p st.

Definition exec_app_comp (t: AnnoTerm) (p:Plc) (st:vm_st) : AM vm_st :=
  app_comp <- build_app_comp t p st ;;
  let app_res := runSt empty_vmst app_comp in
  ret ((snd (app_res))).

Definition exec_app_comp_t (t: Term) (p:Plc) (p':nat) (st:vm_st) : AM vm_st :=
  exec_app_comp (snd (anno t p')) p st.

Definition run_app_comp_ev (t: AnnoTerm) (p:Plc) (st:vm_st) : AM EvidenceC :=
  app_st <- exec_app_comp t p st ;;
  ret (st_ev app_st).

Definition run_app_comp_ev_t (t: Term) (p:Plc) (st:vm_st) : AM EvidenceC :=
  run_app_comp_ev (annotated t) p st.
  

(*
Definition at1 := (asp (ASPC 11 [])).
Definition at2 := (asp (ASPC 22 [])).
Definition aterm := bseq (NONE,NONE) at1 at2.


Definition aterm_ev_comp := run_app_comp_ev_t aterm 0.

Definition ast :=
  mkAM_St [] 0 [((0,11),34); ((0,22),45)].

Definition aterm_res : ((option EvidenceC) * AM_St) := runSt ast aterm_ev_comp.
Compute aterm_res.

Definition aterm_st : AM vm_st := exec_app_comp_t aterm 0 0.
Compute (runSt ast aterm_st).

Definition aet := eval aterm 0 mt.
Compute aet.

Definition evc_st := (run_vm_fresh_t aterm).
Compute evc_st.
Definition evc := st_ev evc_st.
Compute evc.
*)

Definition fromOpt{A:Type} (o:option A) (a:A) : A :=
  match o with
  | Some t => t
  | None => a
  end.

Inductive evMapped : Evidence -> asp_map -> Prop :=
| evMappedMt : forall m, evMapped mt m
| evMappedU : forall p i args e' m,
    evMapped e' m -> 
    (exists j, bound_to m (p,i) j) -> 
    evMapped (uu i args p e') m
| evMappedG : forall e' m p,
    evMapped e' m ->
    evMapped (gg p e') m
| evMappedH : forall e' m p,
    evMapped e' m ->
    evMapped (hh p e') m
| evMappedN : forall e' m nid,
    evMapped e' m ->
    evMapped (nn nid e') m
| evMappedS : forall e1 e2 m,
    evMapped e1 m ->
    evMapped e2 m ->
    evMapped (ss e1 e2) m
| evMappedP : forall e1 e2 m,
    evMapped e1 m ->
    evMapped e2 m ->
    evMapped (pp e1 e2) m.

Inductive allMapped : AnnoTerm -> Plc -> AM_St -> Evidence -> Prop :=
| allMapped_cpy : forall r p st e m,
    m = st_aspmap st ->
    evMapped e m ->
    allMapped (aasp r (CPY)) p st e
| allMapped_asp : forall m st p i r args e,
    m = st_aspmap st ->
    evMapped e m ->
    (exists j, bound_to m (p,i) j) ->
    allMapped (aasp r (ASPC i args)) p st e
| allMapped_sig : forall r p st m e,
    m = st_aspmap st ->
    evMapped e m ->
    allMapped (aasp r (SIG)) p st e
| allMapped_hsh : forall r p st m e,
    m = st_aspmap st ->
    evMapped e m ->
    allMapped (aasp r (HSH)) p st e
| allMapped_at : forall t' p q r st e m,
    m = st_aspmap st ->
    (*evMapped e m -> *) (* TODO: need this? *)
    allMapped t' q st e ->
    allMapped (aatt r q t') p st e
| allMapped_lseq : forall t1 t2 p st r m e,
    m = st_aspmap st ->
    (* evMapped e m -> *)  (* TODO: need this? *)
    allMapped t1 p st e ->
    allMapped t2 p st (eval (unanno t1) p e) ->
    allMapped (alseq r t1 t2) p st e
| allMapped_bseq_nn : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st mt ->
    allMapped (abseq r (NONE,NONE) t1 t2) p st e
| allMapped_bseq_na : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st e ->
    allMapped (abseq r (NONE,ALL) t1 t2) p st e
| allMapped_bseq_an : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st mt ->
    allMapped (abseq r (ALL,NONE) t1 t2) p st e
| allMapped_bseq_aa : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st e ->
    allMapped (abseq r (ALL,ALL) t1 t2) p st e
| allMapped_bpar_nn : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st mt ->
    allMapped (abpar r (NONE,NONE) t1 t2) p st e
| allMapped_bpar_na : forall t1 t2 p st e r,
    allMapped t1 p st mt ->
    allMapped t2 p st e ->
    allMapped (abpar r (NONE,ALL) t1 t2) p st e
| allMapped_bpar_an : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st mt ->
    allMapped (abpar r (ALL,NONE) t1 t2) p st e
| allMapped_bpar_aa : forall t1 t2 p st e r,
    allMapped t1 p st e ->
    allMapped t2 p st e ->
    allMapped (abpar r (ALL,ALL) t1 t2) p st e.



(* NOT true for bseq case, but that's probably ok.. *)
(*
Lemma evMappedSub' : forall t p m e st,
    allMapped t p st e ->
    m = st_aspmap st ->
    evMapped e m.
  (*
    evMapped (eval t p e) m ->
    evMapped e m. *)
Proof.
  induction t; intros.
  -
    destruct a;
      try( cbn in *; inv H; eauto; tauto).
  -
    cbn in *.
    inv H.
    eauto.
  -
    cbn in *.
    inv H.
    eauto.
  -
    cbn in *.
    inv H.
    +
      
    
    
    
    +
      cbn in *.
      inv H.
      eauto.
    +
      
      
    admit.
  -
    cbn in *.
    eauto.
  -
    cbn in *.
    eauto.
       -
         cbn in *.
         inv H.
         destruct s.
         simpl in *.
         destruct s eqn:hi;
           destruct s0 eqn:hey.
         +
           cbn in *.
           eauto.
         +
           cbn in *.
           eauto.
         +
           cbn in *.
           eauto.
         +
           cbn in *.
           Print eval.
           
           
           
         
         
         
     Admitted.
*)

(*
  forall m,
    m = st_aspmap st ->
    evMapped (eval (unanno t) p e) m. 
*)

(*
Definition allMapped (t:AnnoTerm) (p:Plc) (st: AM_St) : Prop :=
  forall aspmap n q i l ,
    measEvent t p (umeas n q i l) -> (* TODO: generalize once measEvent is richer *)
    aspmap = st_aspmap st ->
    exists j,
      bound_to aspmap (q,i) j.
*)

Lemma atgentrace : forall t p e n v1 v a b am_nonceMap am_nonceId st_aspmap ev,
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated t) empty_vmst))) (eval t p e)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (Some v1, a) ->
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated (att n t)) empty_vmst))) (eval (att n t) p e)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (Some v, b) ->
    In ev (st_trace (snd (v1 empty_vmst))) ->
    In ev (st_trace (snd (v empty_vmst))).
Proof.
Admitted.

Lemma fifi : forall t p e n v a b am_nonceMap am_nonceId st_aspmap,
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated t) empty_vmst))) (eval t p e)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (Some v, a) ->
    gen_appraisal_comp
      (st_ev (snd (build_comp (annotated (att n t)) empty_vmst))) (eval t n mt)
      {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} = (None, b) ->
    False.
Proof.
Admitted.


(*
Lemma measEventAt' : forall t n p q ev,
    measEvent (snd (anno (att n t) q)) p ev ->
    measEvent (snd (anno t (S q))) n ev.
Proof.

  induction t; intros.
  - inv H.
    invc H1.
    destruct a;
      try (inv H; inv H1; solve_by_inversion).
    +
      simpl in *.
      invc H0.
      invc H6.
      invc H.
      invc H0.
      simpl.
      econstructor.
      eauto.
      eauto.
  -
    simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    +
    econstructor.
    assumption.
    +
      econstructor.
  - simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    apply evtslseqr.
    assumption.
    econstructor.
  - simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    apply evtsbseqr.
    assumption.
    econstructor.
  - simpl in *.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    simpl in *.
    invc H.
    invc H1.
    repeat find_inversion.
    invc H0.
    invc H5.
    econstructor.
    econstructor.
    eassumption.
    econstructor.
    econstructor.
    apply evtsbparr.
    assumption.
    econstructor.
Defined.
*)

(*
Lemma measEventAt : forall t n p ev,
    measEvent (annotated (att n t)) p ev ->
    measEvent (annotated t) n ev.
Proof.
  intros.
  eapply measEventAt'.
  eapply measEventAt'; eauto.
Defined.
*)


Lemma announ' : forall t p,
    unanno (snd (anno t p)) = t.
Proof.
  induction t; intros; unfold annotated; simpl.
  -
    auto.
  - repeat break_let. simpl.
    edestruct IHt with (p:=(S p)).
    rewrite Heqp0.
    simpl.
    reflexivity.
  - repeat break_let.
    simpl.
    edestruct IHt1 with (p:=p).
    rewrite Heqp0. simpl.
    edestruct IHt2 with (p:=n).
    rewrite Heqp1. simpl. eauto.
  - repeat break_let.
    simpl.
    edestruct IHt1 with (p:=S p).
    rewrite Heqp0. simpl.
    edestruct IHt2 with (p:=n).
    rewrite Heqp1. simpl. eauto.
  - repeat break_let.
    simpl.
    edestruct IHt1 with (p:=S p).
    rewrite Heqp0. simpl.
    edestruct IHt2 with (p:=n).
    rewrite Heqp1. simpl. eauto.
Defined.

Lemma announ : forall t,
    unanno (annotated t) = t.
Proof.
  intros.
  eapply announ'; eauto.
Defined.

Check allMapped.

Lemma allMappedAt : forall r n a p st e,
    allMapped (aatt r n a) p st e ->
    allMapped a n st e.
Proof.
  intros.
  inv H.
  eauto.
Defined.

Check exec_app_comp_t.
Check runSt.

Require Import MonadVMFacts.
Check Term.eval.
Check gen_appraisal_comp.

(*
Lemma app_some' : forall t t' p' e' tr p'' o a_st (app_comp:AM (VM unit)) app_comp_res,
  t = snd (anno t' p') ->
  build_comp t {| st_ev:=mtc; st_trace:=[]; st_pl:=0; st_store:=[]|} =
  (Some tt, {| st_ev:=e'; st_trace:=tr; st_pl:=p''; st_store:=o|}) ->
  allMapped t 0 a_st ->
  app_comp = gen_appraisal_comp e' (Term.eval t' 0 mt) ->
  app_comp_res = runSt a_st app_comp ->
  exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  assert (Ev_Shape e' (Term.eval t' 0 mt)).
  eapply multi_ev_eval; eauto.
  rewrite H.
  Check announ'.
  rewrite announ'.
  reflexivity.
Admitted.
 *)

Check allMapped.
Print allMapped.
Check evMapped.

Lemma evshape_et : forall e et st,
    Ev_Shape e et ->
    evMapped et (st_aspmap st) ->
    exists res, gen_appraisal_comp e et st = (Some res, st).
Proof.
  induction e; intros.
  -
    inv H.
    cbv.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    cbn.
    repeat break_let.
    invc H0.
    destruct_conjs.
    invc H0.
    rewrite H1 in *.
    monad_unfold.
    repeat find_inversion.
    repeat break_let.
    edestruct IHe.
    apply H5.
    eassumption.
    rewrite H0 in *.
    repeat find_inversion.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    eauto.
  -
    inv H.
    cbn.
    monad_unfold.
    eauto.
  -
    cbn.
    invc H.
    invc H0.
    monad_unfold.
    edestruct IHe1.
    apply H3.
    eassumption.
    rewrite H in *.
    repeat break_let.
    edestruct IHe2.
    apply H5.
    eassumption.
    rewrite H0 in *.
    repeat find_inversion.
    eauto.
  -
    cbn.
    invc H.
    invc H0.
    monad_unfold.
    edestruct IHe1.
    apply H3.
    eassumption.
    rewrite H in *.
    repeat break_let.
    edestruct IHe2.
    apply H5.
    eassumption.
    rewrite H0 in *.
    repeat find_inversion.
    eauto.
Defined.

Lemma app_some'' : forall t t' p p' p'' tr tr' o o' e' e et (app_comp: AM (VM unit)) app_comp_res (*app_comp' app_comp_res'*) a_st,
    t = snd (anno t' p') ->
    build_comp t {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} =
    (Some tt, {| st_ev:=e'; st_trace:=tr'; st_pl:=p''; st_store:=o'|}) ->
    Ev_Shape e et ->  (* TODO: maybe don't need this *)
    allMapped t p a_st et ->
    (*evMapped et (st_aspmap a_st) -> *)
    (*app_comp' = gen_appraisal_comp e et ->
    app_comp_res' = runSt a_st app_comp' ->
    (exists st, (fst app_comp_res' = (Some st))) ->  *)
    app_comp = gen_appraisal_comp e' (eval t' p et) ->
    app_comp_res = runSt a_st app_comp ->
    (*Ev_Shape e' (eval t' p mt) -> *)
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  destruct_conjs.
  subst.
  simpl in *.
  repeat find_inversion.
  subst.
  Check trace_irrel_ev'.
  Check restl'.
  Check restl'_2.
  Check suffix_prop.
  assert (exists l, tr' = tr ++ l).
  {
    eapply suffix_prop.

    reflexivity.
    eassumption.
  }
  destruct_conjs.
  rewrite H3 in H0.
  (*
  assert (Ev_Shape e' (eval t' p et)). (* TODO: maybe dont' need this *)
  eapply multi_ev_eval; eauto.
  eapply restl'_2.
  reflexivity.
  eassumption. 
  

  
  erewrite announ'.
  reflexivity. *)
  rewrite <- H3 in *.
  clear H3.
  clear H.
  (*erewrite announ' in *. *)
  generalize dependent p'.
  generalize dependent a_st.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent p''.
  generalize dependent tr.
  generalize dependent p.
  generalize dependent e'.
  generalize dependent e.
  generalize dependent et.
  (*
  generalize dependent o1.
  generalize dependent H4. 
  generalize dependent a0. *)
  generalize dependent a.
  generalize dependent tr'.
  generalize dependent o0.
  induction t'; intros; subst.
  -
    cbn in *.
    repeat break_let.
    monad_unfold.
    repeat find_inversion.
    destruct a; simpl in *;
      repeat find_inversion;
      subst.

    +
      cbn in *.
      invc H2.

     
      inv H1.
      ++
        cbn in *.
        monad_unfold.
        repeat find_inversion.
        eauto.
      ++
        cbn in *.
        monad_unfold.
        invc H3.
        destruct_conjs.
        invc H0.
        cbn in *.
        repeat break_let.
        rewrite H2 in *. clear H2.
        clear H.
        repeat find_inversion.
        monad_unfold.
        repeat find_inversion.
        repeat break_let.
        repeat find_inversion.
        vmsts.
        assert (a = a1).
        {
          Lemma gen_const : forall e et a o a',
            gen_appraisal_comp e et a = (o,a') ->
            a = a'.
          Proof.
            induction e; intros.
            -
              cbn in *.
              destruct et;
                try (monad_unfold; repeat find_inversion; reflexivity).
            -
              cbn in *.
              destruct et;
                try (monad_unfold; repeat find_inversion; reflexivity).
              monad_unfold.
              cbn in *.
              repeat break_let.
              repeat find_inversion.
              repeat break_match;
                try solve_by_inversion.
              +
                repeat find_inversion.
                monad_unfold.
                repeat find_inversion.
                eauto.
              +
                monad_unfold.
                repeat find_inversion.
                eauto.
              +
                repeat find_inversion.
                monad_unfold.
                repeat find_inversion.
                eauto.
            -
              cbn in *.
              destruct et;
                try (monad_unfold; repeat find_inversion; reflexivity).
            -
              cbn in *.
              destruct et;
                try (monad_unfold; repeat find_inversion; reflexivity).
            -
              cbn in *.
              destruct et;
                try (monad_unfold; repeat find_inversion; reflexivity).
            -
              cbn in *.
              destruct et;
                try (monad_unfold; repeat find_inversion; reflexivity).
              monad_unfold.
              repeat break_match;
                try solve_by_inversion.
              +
                repeat find_inversion.
                assert (a = a0).
                eauto.
                subst.
                eauto.
              +
                repeat find_inversion.
                assert (a = a0) by eauto.
                subst.
                eauto.
              +
                repeat find_inversion.
                eauto.
            -
               cbn in *.
              destruct et;
                try (monad_unfold; repeat find_inversion; reflexivity).
              monad_unfold.
              repeat break_match;
                try solve_by_inversion.
              +
                repeat find_inversion.
                assert (a = a0).
                eauto.
                subst.
                eauto.
              +
                repeat find_inversion.
                assert (a = a0) by eauto.
                subst.
                eauto.
              +
                repeat find_inversion.
                eauto.
          Defined.

          eapply gen_const; eauto.

        }
        subst.


        edestruct evshape_et.
        inv H1.
        apply H0.
        apply H8.
        rewrite H in *.
        repeat find_inversion.
        eauto.

      ++
        cbn in *.
        monad_unfold.
        repeat find_inversion.
        eauto.
      ++
        cbn in *.
        monad_unfold.
        repeat find_inversion.
        eauto.
      ++
        cbn in *.
        monad_unfold.
        repeat find_inversion.
        eauto.
      ++
        cbn in *.
        monad_unfold.
        inv H3.
        Check evshape_et.
        edestruct evshape_et with (e:=e1); eauto.
        edestruct evshape_et with (e:=e2); eauto.
        rewrite H2 in *.
        rewrite H5 in *.
        repeat find_inversion.
        eauto.
      ++
        cbn in *.
        monad_unfold.
        inv H3.
        edestruct evshape_et with (e:=e1); eauto.
        edestruct evshape_et with (e:=e2); eauto.
        rewrite H2 in *.
        rewrite H5 in *.
        repeat find_inversion.
        eauto.
    +
      cbn in *.
      monad_unfold.
      invc H2.
      destruct_conjs.
      invc H.
      cbn in *.
      rewrite H0 in *.
      monad_unfold.
      repeat break_let.
      repeat find_inversion.
      edestruct evshape_et.
      eassumption.
      eassumption.
      rewrite H in *.
      repeat find_inversion.
      eauto.
    +
      cbn in *.
      monad_unfold.
      repeat find_inversion.
      eauto.
    +
      cbn in *.
      monad_unfold.
      repeat find_inversion.
      eauto.
  -
    cbn in *.
    repeat break_let.
    simpl in *.

    
      
      
      
      monad_unfold.
      cbn in *.
      dohtac.
      
      repeat break_let.
      monad_unfold.
      repeat find_inversion.

      eapply IHt'.
      eassumption.
      apply H4.
      rewrite Heqp0.
      simpl.
      eapply build_comp_at.
      invc H2.
      rewrite Heqp0.
      simpl.
      eassumption.
  -
    Check alseq_decomp.
    assert (a_st = a).
    {
     
      eapply gen_const; eauto.
    }
    subst.
    cbn in *.
    repeat break_let.
    (*
    assert (unanno a = t'1).
    {
      erewrite <- announ'.
      rewrite Heqp0.
      simpl.
      reflexivity.
    }
*)
    
    unfold snd in *.

    
    assert (alseq (p', n0) a0 a1 = snd (anno (lseq t'1 t'2) p')).
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        rewrite Heqp3 in *.
        repeat find_inversion.
        reflexivity.
      }
     
    
    assert (exists l, tr' = tr ++ l).
    {
      eapply suffix_prop.
      reflexivity.

      rewrite <- H.
      eassumption.
    }
    destruct_conjs.

    



    
    Check alseq_decomp.
    edestruct alseq_decomp with (r:=(p',n0)).
    cbn.
    repeat break_let.
    simpl.
    repeat find_inversion.
    rewrite Heqp0 in Heqp2.
    repeat find_inversion.
    rewrite Heqp1 in *.
    repeat find_inversion.
    reflexivity.

    rewrite H5 in *.
    eapply restl'_2.
    eassumption.
    eassumption.
    clear H.
    
    
    destruct_conjs.
    

    destruct (gen_appraisal_comp x (eval t'1 p et) a) eqn:hi.



    destruct IHt'1 with (a:=a) (a_st:=a) (tr':=H6) (o0:=o1) (et:=et) (e:=e) (e':=x) (p:=p) (tr:=nil (A:=Ev)) (p'':=p'') (o':=H7) (o:=o) (p':=p').

    Print allMapped.



     (*

    Lemma evMappedSub' : forall t1 t2 p m et,
        evMapped (eval t2 p (eval t1 p et)) m ->
        evMapped et m -> 
        evMapped (eval t1 p et) m.
    Proof.
      induction t1;
        destruct t2; intros.
      -
        destruct a;
          try (cbn in *; try (econstructor); eauto; tauto).
        +
          cbn in *.
          econstructor.
          eauto.
          cbn in *.
          destruct a0;
            try (cbn in *; eauto; tauto).
          ++
            cbn in *.
            inv H.
            eauto.
          ++
            cbn in *.
            inv H.
            inv H6.
            destruct_conjs.
            eauto.
          ++
            inv H.
            inv H4.
            eauto.
          ++
            inv H.
            inv H4.
            eauto.
      -
        cbn in *.
        destruct a;
          try (cbn in *; try (econstructor); eauto; tauto).
        + cbn in *.
          econstructor.
          eauto.
          cbn in *.
          
          
        +
          cbn in *.
        
          cbn in *.
          econstructor.
          eauto.
        +
          cbn in *.
          econstructor.
          eauto.
        +
          
          cbn in *.
          destruct a0;
            try (cbn in *; eauto; tauto).
          
          
            
            
            
            
            destruct_conjs
              eauto.
        + cbn in *.
          eauto.
        +
          cbn in *.
          econstructor.
          eauto.
          inv H
          
          
        
    Admitted.
      *)
     
(*
    eapply evMappedSub'; eauto. *)

    eassumption.
    unfold runSt in *.


    assert (a = a2).
    {
      eapply gen_const; eauto.
    }
    congruence.

    rewrite Heqp0.
    (*
    inv H1.

    repeat break_let.
    repeat find_inversion.
    eassumption.
    repeat break_let.
    repeat find_inversion. *)
    
    assert (H = p'').
    {
      symmetry.
      erewrite <- pl_immut in *.
      rewrite H10.
      simpl.
      reflexivity.
    }
    subst.
    eassumption.

    rewrite Heqp0.
    inv H2.
    assert (a = a2).
    {
      eapply gen_const; eauto.
    }
    subst.
    eassumption.


    Check multi_ev_eval.
    (*
multi_ev_eval
     : forall (t : AnnoTerm) (t' : Term) (n : nat) (tr : list Ev) (e e' : EvidenceC) (p p' : nat)
         (o o' : ev_store) (es e's : Evidence),
       t = snd (anno t' n) ->
       build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
       (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}) ->
       Ev_Shape e es -> eval (unanno t) p es = e's -> Ev_Shape e' e's
     *)


    (*




    
    
    apply multi_ev_eval with (t:=a) (t':=t'1) (n:=p') (tr:=H10) (e:=e) (e':=x) (p:=p) (p':= H11) (o:=o) (o':=H12) (es:=et).
                                                                                            
    rewrite Heqp0.
    reflexivity. *)


    (*
    simpl.
    eassumption.
    eassumption.
    simpl.

    rewrite Heqp0.
    assert (H10 = p'').
    {
      admit.
    }
    rewrite H16 in *.
    
    eassumption.
     *)
    

    (*
    subst.
    repeat find_inversion.
    reflexivity.

    (*
    Lemma evMappedSub : forall t1 t2 p m et,
      evMapped (eval t2 p (eval t1 p et)) m ->
      evMapped (eval t1 p et) m.
    Proof.
      induction t1;
        induction t2; 
        intros.
      -
        destruct a;
          destruct a0;
          try (cbn in *; try (inv H); eassumption).
      -
        cbn in *.
        eapply IHt2.
        eassumption.
        
        + cbn in *.
          inv H.
          
        +
          cbn in *.
          eassumption.
        + cbn in *.
          inv H
          eassumption.
        +
          cbn in *.
          inv H.
          eassumption.
        + cbn in *.
          inv H.
          eassumption.
        + cbn in *.
          inv H.
          eassumption.
      -
        cbn in *.
        eapply IHt.
        eauto.
      -
        cbn in *.
        assert (evMapped (eval t1 p e) m).
        eapply IHt2.
        eassumption.
        eapply IHt1.
        eassumption.
      -
        cbn in *.
        inv H.
        destruct s.
        simpl in *.
        destruct s;
          destruct s0;
          cbn in *; try eauto.
        +
          (*
          eapply IH
        +
          eauto.
    Admitted.
*)
*)

    
    
    Lemma evMappedSub : forall t p e m,
      evMapped (eval t p e) m ->
      evMapped e m.
    Proof.
      induction t; intros.
      -
        destruct a.
        + cbn in *.
          eassumption.
        +
          cbn in *.
          inv H.
          eassumption.
        + cbn in *.
          inv H.
          eassumption.
        + cbn in *.
          inv H.
          eassumption.
      -
        cbn in *.
        eapply IHt.
        eauto.
      -
        cbn in *.
        assert (evMapped (eval t1 p e) m).
        eapply IHt2.
        eassumption.
        eapply IHt1.
        eassumption.
      -
        cbn in *.
        inv H.
        destruct s.
        simpl in *.
        destruct s;
          destruct s0;
          cbn in *.
        +
          eauto.
        +
          eauto.
        +
          eauto.
        +
          assert (evMapped mt m).
          eauto.
          inversion H0.
          
          
          
          (*
          eapply IH
        +
          eauto.
          
        
        eassumption
        assert (evMapped (eval t1 p e) m).
        eapply IHt1
        eapply 
        
        
          
          
          
          
          
        
      inv H.
      -
        admit.
      -
        
        *)
        
    Admitted.

    eapply evMappedSub; eauto.
     
    
    unfold runSt.
    rewrite hi.
    assert (a2 = a_st).
    {
      admit.
    }
    rewrite H17.
    reflexivity.
    repeat break_let.
    
    
    repeat find_inversion.
    eassumption.
     *)
    

















    
    




    subst.
    
    eapply IHt'2 with (e:=x) (p':=n).

    eapply multi_ev_eval.
    reflexivity.

    rewrite Heqp0.
    simpl.
    eassumption.
    eassumption.
    reflexivity.
    erewrite announ'.
    eassumption.
    rewrite Heqp1.
    assert (p = H).
    {
      symmetry.
      erewrite <- pl_immut in *.
      rewrite H8.
      simpl.
      reflexivity.
    }
    subst.
    eassumption.
    rewrite Heqp1.
    inv H2.
    rewrite announ'.
    assert (unanno a0 = t'1).
    erewrite <- announ'.
    rewrite Heqp0.
    simpl.
    reflexivity.
    subst.
    eassumption.
    
    


(*
    
    unfold runSt.
    symmetry.
    
    apply hi.
    eassumption.
    repeat break_let.
    repeat find_inversion.
    
    inv H1.
    eassumption.
    repeat break_let.
    repeat find_inversion.
    assert (p = H9).
    {
      admit.
    }
    subst.
    eassumption.

*)
  
    (*
    
    (*
    eapply evMappedSub'; eauto. *)

    (*






    
    eapply multi_ev_eval.
    rewrite Heqp0.
    reflexivity.
    simpl.
    eassumption.
    eassumption.
    reflexivity.
    simpl.
    rewrite H.
    eassumption.
    simpl.
    rewrite H.
    eassumption.
    simpl.
    rewrite H.
     *)
    

    unfold runSt.
    rewrite hi.
    rewrite H16.
    reflexivity.
    simpl.
    rewrite H7.
    reflexivity.
    repeat break_let.
    rewrite Heqp2 in *.
    repeat find_inversion.
    assert (p = H10).
    {
      admit.
    }
    rewrite H.
    eassumption.
     *)
    
    
  -

    assert (a = a_st).
    {
      symmetry.
      eapply gen_const; eauto.
    }
    subst.
    cbn in *.
    repeat break_let.
    (*
    assert (unanno a = t'1).
    {
      admit.
    }

    assert (unanno a0 = t'2).
    {
      admit.
    }
     *)
    
    
    unfold snd in *.

    (*
    assert (abseq (p', (S n0)) s a a0 = snd (anno (bseq s t'1 t'2) p')).
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        subst.
        repeat find_inversion.
      
        rewrite Heqp3 in *.
        repeat find_inversion.
        reflexivity.
      }
     *)
    



      cbn in *.
      monad_unfold.
      repeat break_let.
      repeat find_inversion.
      (*
      inversion Heqp6.
      rewrite H10 in *. clear H10.
      rewrite H11 in *. clear H11.

      repeat find_inversion. *)
      simpl in *.
      (*
      rewrite Heqp3 in *.
      repeat find_inversion. *)
      destruct o5; try solve_by_inversion.
      repeat find_inversion.
      destruct o9; try solve_by_inversion.
      repeat find_inversion.
   
      simpl in *.
      cbn in *.
      monad_unfold.
      
(*
      Lemma annoAll :
        forall a,
          well_formed a ->
        exists n t', a = snd (anno t' n).
      Proof.
        induction a; intros.
        -
          destruct a; destruct r.
          + 
            exists n.
            exists (asp CPY).
            cbn.
            inv H.
            simpl in *.
            congruence.
          + exists n0.
            exists (asp (ASPC n l)).
            cbn.
            inv H.
            repeat find_inversion.
            simpl in *.
            subst.
            reflexivity.
          +
            exists n.
            exists (asp SIG).
            cbn.
            inv H.
            simpl in *.
            subst.
            reflexivity.
          +
            exists n.
            exists (asp HSH).
            cbn.
            inv H.
            simpl in *.
            subst.
            reflexivity.
        -
          inv H.
          destruct r.
          simpl in *.
          edestruct IHa.
          eassumption.
          destruct_conjs.
          eexists n0.
          exists (att n (unanno a)).
          cbn.
          repeat break_let.
          simpl.
          subst.
          simpl.
          rewrite announ' in *.
          eexists (S n0).
          eexists (unanno a).
          edestruct IHa.
          eassumption.
          destruct_conjs.
          rewrite H1.
          rewrite announ'.
          rewrite <- H1.
          eexists x.
          eexists (unanno a).
          rewrite H1.
          rewrite announ'.
          rewrite <- H1.
          exists (fst r).
          exists (unanno a).

          edestruct IHa.
          eassumption.
          destruct_conjs.
          rewrite H1.
          rewrite announ'.
          
            
            
            
            
            eexists.
            exists n.
            eexists.
            unfold anno.
*)
            
          (*
      assert (exists t' n, a = snd (anno t' n)).
      {
        repeat eexists.
        cbn.
          admit.
        }
      destruct_conjs.
           *)
      
      vmsts.
       
      
        (*
        assert (exists l, st_trace1 = (tr ++ [Term.split p' p]) ++ l).
        {
          admit.
        }
        destruct_conjs.
        rewrite H11 in Heqp8.
        clear H11.
         *)
      simpl in *.
      invc H2.
      +
    
      

        

        
    

      (*
      destruct s0 eqn:hi;
        destruct s1 eqn:he. *)
        cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp st_ev0 (eval t'1  p mt) a_st) eqn:ghi.
        destruct (gen_appraisal_comp st_ev  (eval t'2  p mt) a_st) eqn:hhi.
        
        edestruct IHt'1.
        eapply mtt.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eassumption.
        rewrite Heqp0.
        eassumption.
        (*
        repeat break_let.
        repeat find_inversion.
        erewrite announ' in *.
        repeat find_inversion.
        rewrite Heqp3 in *.
        simpl in *.
        eassumption.
        repeat break_let.
        erewrite announ' in *.
        rewrite Heqp3 in *.
        simpl in *.
        eassumption.
         *)
        

        (*
        (*
        eapply mtt. *)
        unfold runSt in *.
        
        eassumption.
        unfold runSt.
        symmetry.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        rewrite announ' in *.
        rewrite Heqp0 in *.
        simpl in *.
        repeat find_inversion.
        eassumption.
         *)


        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        eapply mtt.
        symmetry.
        eassumption.
        rewrite Heqp1.
        (*
        eassumption.
        repeat break_let.
        erewrite announ' in *.
        rewrite Heqp4 in *.
        simpl in *.
        repeat find_inversion. *)
        assert (p = st_pl0).
        {
          symmetry.
          erewrite <- pl_immut in *.
          rewrite Heqp6.
          simpl.
          reflexivity.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.
        (*

        
        repeat break_let.
        erewrite announ' in *.
        repeat find_inversion.
        eassumption. *)

        (*
        
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12.
         *)
        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.



      +
        cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp st_ev0 (eval t'1  p mt) a_st) eqn:ghi.
        destruct (gen_appraisal_comp st_ev  (eval t'2  p et) a_st) eqn:hhi.
        
        edestruct IHt'1.
        eapply mtt.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eassumption.
        rewrite Heqp0.
        eassumption.
        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp1.

        assert (p = st_pl0).
        {
          symmetry.
          erewrite <- pl_immut in *.
          rewrite Heqp6.
          simpl.
          reflexivity.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.

        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.
      +
                cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp st_ev0 (eval t'1  p et) a_st) eqn:ghi.
        destruct (gen_appraisal_comp st_ev  (eval t'2  p mt) a_st) eqn:hhi.
        
        edestruct IHt'1.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eassumption.
        rewrite Heqp0.
        eassumption.
        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        apply mtt.
        symmetry.
        eassumption.
        rewrite Heqp1.

        assert (p = st_pl0).
        {
          symmetry.
          erewrite <- pl_immut in *.
          rewrite Heqp6.
          simpl.
          reflexivity.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.

        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.
      +
        cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp st_ev0 (eval t'1  p et) a_st) eqn:ghi.
        destruct (gen_appraisal_comp st_ev  (eval t'2  p et) a_st) eqn:hhi.
        
        edestruct IHt'1.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eassumption.
        rewrite Heqp0.
        eassumption.
        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp1.

        assert (p = st_pl0).
        {
          symmetry.
          erewrite <- pl_immut in *.
          rewrite Heqp6.
          simpl.
          reflexivity.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.

        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.
  -
    assert (a = a_st).
    {
      symmetry.
      eapply gen_const; eauto.
    }
    subst.
    cbn in *.
    repeat break_let.
    (*
    assert (unanno a = t'1).
    {
      admit.
    }

    assert (unanno a0 = t'2).
    {
      admit.
    }
     *)
    
    
    unfold snd in *.

    (*
    assert (abseq (p', (S n0)) s a a0 = snd (anno (bseq s t'1 t'2) p')).
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        subst.
        repeat find_inversion.
      
        rewrite Heqp3 in *.
        repeat find_inversion.
        reflexivity.
      }
     *)
    



      cbn in *.
      monad_unfold.
      repeat break_let.
      repeat find_inversion.
      (*
      inversion Heqp6.
      rewrite H10 in *. clear H10.
      rewrite H11 in *. clear H11.

      repeat find_inversion. *)
      simpl in *.
      (*
      rewrite Heqp3 in *.
      repeat find_inversion. *)
      destruct o5; try solve_by_inversion.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      unfold get_store_at in *.
      monad_unfold.
      assert (PeanoNat.Nat.eqb (fst (range a)) (fst (range a0)) = false).
      {
        assert (
            exists r b,
              abpar r b a a0 = snd(anno (bpar (s0,s1) t'1 t'2) p')).
        {
          eexists.
          eexists.
          cbn.
          repeat break_let.
          simpl.
          repeat find_inversion.
          rewrite Heqp8 in *.
          repeat find_inversion.
          reflexivity.
        }
        destruct_conjs.
        eapply h; eauto.
      }
      rewrite H in *.
      dohtac.
      repeat find_inversion.
      repeat break_let.
      simpl in *.
      dohtac.
      repeat find_inversion.
      
   
      simpl in *.
      cbn in *.
      monad_unfold.
      
(*
      Lemma annoAll :
        forall a,
          well_formed a ->
        exists n t', a = snd (anno t' n).
      Proof.
        induction a; intros.
        -
          destruct a; destruct r.
          + 
            exists n.
            exists (asp CPY).
            cbn.
            inv H.
            simpl in *.
            congruence.
          + exists n0.
            exists (asp (ASPC n l)).
            cbn.
            inv H.
            repeat find_inversion.
            simpl in *.
            subst.
            reflexivity.
          +
            exists n.
            exists (asp SIG).
            cbn.
            inv H.
            simpl in *.
            subst.
            reflexivity.
          +
            exists n.
            exists (asp HSH).
            cbn.
            inv H.
            simpl in *.
            subst.
            reflexivity.
        -
          inv H.
          destruct r.
          simpl in *.
          edestruct IHa.
          eassumption.
          destruct_conjs.
          eexists n0.
          exists (att n (unanno a)).
          cbn.
          repeat break_let.
          simpl.
          subst.
          simpl.
          rewrite announ' in *.
          eexists (S n0).
          eexists (unanno a).
          edestruct IHa.
          eassumption.
          destruct_conjs.
          rewrite H1.
          rewrite announ'.
          rewrite <- H1.
          eexists x.
          eexists (unanno a).
          rewrite H1.
          rewrite announ'.
          rewrite <- H1.
          exists (fst r).
          exists (unanno a).

          edestruct IHa.
          eassumption.
          destruct_conjs.
          rewrite H1.
          rewrite announ'.
          
            
            
            
            
            eexists.
            exists n.
            eexists.
            unfold anno.
*)
            
          (*
      assert (exists t' n, a = snd (anno t' n)).
      {
        repeat eexists.
        cbn.
          admit.
        }
      destruct_conjs.
           *)
      
      vmsts.
       
      
        (*
        assert (exists l, st_trace1 = (tr ++ [Term.split p' p]) ++ l).
        {
          admit.
        }
        destruct_conjs.
        rewrite H11 in Heqp8.
        clear H11.
         *)
      simpl in *.
      invc H2.


    +
        cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a  mtc) (eval t'1  p'' mt) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a0 mtc) (eval t'2  p'' mt) a_st) eqn:hhi.
        
        edestruct IHt'1.
        eapply mtt.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eapply build_comp_par.
       
        rewrite Heqp0.
        eassumption.
        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        apply mtt.
        symmetry.
        eassumption.
        rewrite Heqp1.
        apply build_comp_par.
        rewrite Heqp1.
        eassumption.

        (*

        assert (p = st_pl0).
        {
          admit.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.
         *)
        

        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
         
        
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.

    +
              cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a  mtc) (eval t'1  p'' mt) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a0 e) (eval t'2  p'' et) a_st) eqn:hhi.
        
        edestruct IHt'1.
        eapply mtt.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eapply build_comp_par.
       
        rewrite Heqp0.
        eassumption.
        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp1.
        apply build_comp_par.
        rewrite Heqp1.
        eassumption.

        (*

        assert (p = st_pl0).
        {
          admit.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.
         *)
        

        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
         
        
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.
    +
        cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a  e) (eval t'1  p'' et) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a0 mtc) (eval t'2  p'' mt) a_st) eqn:hhi.
        
        edestruct IHt'1.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eapply build_comp_par.
       
        rewrite Heqp0.
        eassumption.
        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        apply mtt.
        symmetry.
        eassumption.
        rewrite Heqp1.
        apply build_comp_par.
        rewrite Heqp1.
        eassumption.

        (*

        assert (p = st_pl0).
        {
          admit.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.
         *)
        

        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
         
        
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.
    +
        cbn in *.
        repeat dunit.
        vmsts.
        simpl in *.
        unfold runSt in *.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a e) (eval t'1  p'' et) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a0 e) (eval t'2  p'' et) a_st) eqn:hhi.
        
        edestruct IHt'1.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp0.
        eapply build_comp_par.
       
        rewrite Heqp0.
        eassumption.
        
        subst.
       
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        apply H1.
        symmetry.
        eassumption.
        rewrite Heqp1.
        apply build_comp_par.
        rewrite Heqp1.
        eassumption.

        (*

        assert (p = st_pl0).
        {
          admit.
        }
        subst.
        eassumption.
        rewrite Heqp1.
        eassumption.
         *)
        

        assert (a1 = a3).
        {
          symmetry.
          eapply gen_const; eauto.
        }
         
        
        subst.
        rewrite hhi in *.
        repeat find_inversion.
        eauto.
        Unshelve.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
Defined.

      
      
      
    
        
        
        

















        


        cbn in *.
      repeat dunit.

      destruct (gen_appraisal_comp st_ev1 (eval (unanno a) p et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev0 (eval (unanno a1) p et) a2) eqn:hhi.
        
        edestruct IHt'1.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        rewrite announ' in *.
        rewrite Heqp0 in *.
        simpl in *.
        repeat find_inversion.
        eassumption.
        subst.
        
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          symmetry.
          eapply gen_const; eauto.
          admit.
        }
        rewrite H2 in *. clear H2.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12.

        subst.
        repeat find_inversion.
        eexists.
        eauto.



        
        cbn in *.
      repeat dunit.

      destruct (gen_appraisal_comp st_ev1 (eval (unanno a) p et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev0 (eval (unanno a1) p mt) a2) eqn:hhi.
        
        edestruct IHt'1.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        rewrite announ' in *.
        rewrite Heqp0 in *.
        simpl in *.
        repeat find_inversion.
        eassumption.
        subst.
        
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        eapply mtt.
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12.

        subst.
        repeat find_inversion.
        eexists.
        eauto.


                
        cbn in *.
      repeat dunit.

      destruct (gen_appraisal_comp st_ev1 (eval (unanno a) p mt) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev0 (eval (unanno a1) p et) a2) eqn:hhi.
        
        edestruct IHt'1.
        eapply mtt.
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        rewrite announ' in *.
        rewrite Heqp0 in *.
        simpl in *.
        repeat find_inversion.
        eassumption.
        subst.
        
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12.

        subst.
        repeat find_inversion.
        eexists.
        eauto.
  -
    

    
    assert (a = a_st).
    {
      admit.
    }
    subst.
    cbn in *.
    repeat break_let.
    assert (unanno a = t'1).
    {
      admit.
    }

    assert (unanno a1 = t'2).
    {
      admit.
    }
    
    unfold snd in *.

    assert (abpar (p', (S n0)) s a a1 = snd (anno (bpar s t'1 t'2) p')).
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        subst.
        repeat find_inversion.
      
        rewrite Heqp3 in *.
        repeat find_inversion.
        reflexivity.
      }



      cbn in *.
      monad_unfold.
      repeat break_let.
      inversion Heqp6.
      rewrite H10 in *. clear H10.
      rewrite H11 in *. clear H11.

      repeat find_inversion.
      rewrite Heqp3 in *.
      repeat find_inversion.
      destruct o5; try solve_by_inversion.
      repeat find_inversion.
      simpl in *.
      unfold get_store_at in *.
      monad_unfold.
      dohtac.
      repeat break_let.
      repeat find_inversion.
      assert (
          PeanoNat.Nat.eqb (fst (range a)) (fst (range a1)) = false).
      admit.
      rewrite H in *.
      repeat find_inversion.
      simpl in *.
      dohtac.
      repeat find_inversion.
      monad_unfold.
      monad_unfold.
      invc H6.
      invc H2.

      (*
      assert (exists t' n, a = snd (anno t' n)).
        {
          admit.
        }
        destruct_conjs. *)
        vmsts.
        (*
        assert (exists l, st_trace1 = (tr ++ [Term.split p' p]) ++ l).
        {
          admit.
        }
        destruct_conjs.
        rewrite H11 in Heqp8.
        clear H11. *)

        
    

      
      destruct s0 eqn:hi;
        destruct s1 eqn:he.
      4: {
        cbn in *.
        repeat dunit.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a mtc) (eval (unanno a) p'' mt) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a1 mtc) (eval (unanno a1) p'' mt) a2) eqn:hhi.
        repeat break_let.
        

        edestruct IHt'1 with (p':=(S p')) (p:=p'') (tr':=parallel_vm_events a p'') (a0:=a_st) (a1:=a2) (o1:=o0) (et:=mt) (e:=mtc) (e':=parallel_att_vm_thread a mtc) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))).
        eapply mtt.
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        
        subst.

        unfold runSt in *.
        rewrite ghi in *.
        repeat break_let.
        repeat find_inversion.

        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H0 in *.

        edestruct IHt'2 with (p':=n) (p:=p'') (tr':=parallel_vm_events a1 p'') (a:=a_st) (a0:=a3) (o1:=o2) (et:=mt) (e:=mtc) (e':=parallel_att_vm_thread a1 mtc) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))) (a_st:=a_st).
        eapply mtt.
        eassumption.
        eassumption.
        cbv.
        
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        Check build_comp_par.
        (*
          parallel_vm_events t n;
         *)

        
        subst.
        repeat find_inversion.
        eexists.
        eauto.
      }


        cbn in *.
        repeat dunit.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a e) (eval (unanno a) p'' et) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a1 e) (eval (unanno a1) p'' et) a2) eqn:hhi.
        repeat break_let.
        
        edestruct IHt'1 with (p':=(S p')) (p:=p'') (tr':=parallel_vm_events a p'') (a0:=a_st) (a1:=a2) (o1:=o0) (et:=et) (e:=e) (e':=parallel_att_vm_thread a e) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))).
        eassumption.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        
        subst.

        unfold runSt in *.
        rewrite ghi in *.
        repeat break_let.
        repeat find_inversion.

        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H0 in *.

        edestruct IHt'2 with (p':=n) (p:=p'') (tr':=parallel_vm_events a1 p'') (a:=a_st) (a0:=a3) (o1:=o2) (et:=et) (e:=e) (e':=parallel_att_vm_thread a1 e) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))) (a_st:=a_st).
        eassumption.
        eassumption.
        eassumption.
        rewrite H4.
        
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        Check build_comp_par.
        (*
          parallel_vm_events t n;
         *)

        
        subst.
        repeat find_inversion.
        eexists.
        eauto.
      
          

        cbn in *.
        repeat dunit.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a e) (eval (unanno a) p'' et) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a1 mtc) (eval (unanno a1) p'' mt) a2) eqn:hhi.
        repeat break_let.
        
        edestruct IHt'1 with (p':=(S p')) (p:=p'') (tr':=parallel_vm_events a p'') (a0:=a_st) (a1:=a2) (o1:=o0) (et:=et) (e:=e) (e':=parallel_att_vm_thread a e) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))).
        eassumption.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        
        subst.

        unfold runSt in *.
        rewrite ghi in *.
        repeat break_let.
        repeat find_inversion.

        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H0 in *.

        edestruct IHt'2 with (p':=n) (p:=p'') (tr':=parallel_vm_events a1 p'') (a:=a_st) (a0:=a3) (o1:=o2) (et:=mt) (e:=mtc) (e':=parallel_att_vm_thread a1 mtc) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))) (a_st:=a_st).
        econstructor.
        eassumption.
        eassumption.
        cbv.
        reflexivity.

        unfold runSt.
        symmetry.
        eassumption.
        
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        Check build_comp_par.
        (*
          parallel_vm_events t n;
         *)

        
        subst.
        repeat find_inversion.
        eexists.
        eauto.


        cbn in *.
        repeat dunit.

        destruct (gen_appraisal_comp (parallel_att_vm_thread a mtc) (eval (unanno a) p'' mt) a_st) eqn:ghi.
        destruct (gen_appraisal_comp (parallel_att_vm_thread a1 e) (eval (unanno a1) p'' et) a2) eqn:hhi.
        repeat break_let.
        
        edestruct IHt'1 with (p':=(S p')) (p:=p'') (tr':=parallel_vm_events a p'') (a0:=a_st) (a1:=a2) (o1:=o0) (et:=mt) (e:=mtc) (e':=parallel_att_vm_thread a mtc) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))).
        econstructor.
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        
        subst.

        unfold runSt in *.
        rewrite ghi in *.
        repeat break_let.
        repeat find_inversion.

        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H0 in *.

        edestruct IHt'2 with (p':=n) (p:=p'') (tr':=parallel_vm_events a1 p'') (a:=a_st) (a0:=a3) (o1:=o2) (et:=et) (e:=e) (e':=parallel_att_vm_thread a1 e) (tr:=nil (A:=Ev)) (p'':=p'') (o:=nil (A:=(nat*EvidenceC))) (a_st:=a_st).
        
        eassumption.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.

        unfold runSt.
        symmetry.
        eassumption.
        
        repeat break_let.
        repeat find_inversion.
        Check build_comp_par.
        erewrite build_comp_par.
        reflexivity.
        Check build_comp_par.
        (*
          parallel_vm_events t n;
         *)

        
        subst.
        repeat find_inversion.
        eexists.
        eauto.
        Unshelve.
        eauto.




















      
        unfold runSt in *.
        rewrite ghi in *.
        repeat break_let.
        repeat find_inversion.









































        
        edestruct IHt'2.
        eapply mtt.
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H3 in *. clear H3.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        eapply build_comp_par.

        (*
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12. *)

        subst.
        repeat find_inversion.
        eexists.
        eauto.
      }



        cbn in *.
      repeat dunit.

      destruct (gen_appraisal_comp st_ev1 (eval (unanno a) p et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev0 (eval (unanno a1) p et) a2) eqn:hhi.
        
        edestruct IHt'1.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        rewrite announ' in *.
        rewrite Heqp0 in *.
        simpl in *.
        repeat find_inversion.
        eassumption.
        subst.
        
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12.

        subst.
        repeat find_inversion.
        eexists.
        eauto.



        
        cbn in *.
      repeat dunit.

      destruct (gen_appraisal_comp st_ev1 (eval (unanno a) p et) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev0 (eval (unanno a1) p mt) a2) eqn:hhi.
        
        edestruct IHt'1.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        rewrite announ' in *.
        rewrite Heqp0 in *.
        simpl in *.
        repeat find_inversion.
        eassumption.
        subst.
        
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        eapply mtt.
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12.

        subst.
        repeat find_inversion.
        eexists.
        eauto.


                
        cbn in *.
      repeat dunit.

      destruct (gen_appraisal_comp st_ev1 (eval (unanno a) p mt) a_st) eqn:ghi.
      destruct (gen_appraisal_comp st_ev0 (eval (unanno a1) p et) a2) eqn:hhi.
        
        edestruct IHt'1.
        eapply mtt.
        eassumption.
        eassumption.
        cbv.
        reflexivity.
        unfold runSt.
        symmetry.
        eassumption.
        repeat break_let.
        repeat find_inversion.
        rewrite announ' in *.
        rewrite Heqp0 in *.
        simpl in *.
        repeat find_inversion.
        eassumption.
        subst.
        
        repeat break_let.
        repeat find_inversion.

        edestruct IHt'2.
        eapply H1.
        eassumption.
        eassumption.
        rewrite H4.
        reflexivity.
        unfold runSt.
        symmetry.
        assert (a2 = a_st).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        eassumption.
        Check announ'.
        rewrite Heqp3.
        assert (p = st_pl1).
        {
          admit.
        }
        rewrite H2 in *. clear H2.
        
        apply Heqp12.

        subst.
        repeat find_inversion.
        eexists.
        eauto.


        

      
      


        
        erewrite announ'.
        repeat break_let.
        rewrite announ' in *.
        rewrite announ in *.
        subst

        
        
        reflexivity.
        cbn in *.

        
        eapply multi_ev_eval.
        apply H2.
        eapply restl'.
        eassumption.
        apply Heqp8.
        econstructor.
        reflexivity.
        
        Check announ.
      
        rewrite H2 in *.
        eassumption.
        
        erewrite <- announ' in *.
        assert (
      

      edestruct IHt'1.
      apply H1.
      

    
    
    

Admitted.


(*








    



    
    destruct IHt'1 with (a:=a_st) (a0:=a_st) (tr':=H10) (H5:=H5) (o1:=o0) (et:=et) (e:=e) (e':=x) (p:=p) (tr:=nil (A:=Ev)) (p'':=H11) (o':=H12) (o:=o) (a_st:=a_st) (p':=p').
    apply H1.
    3: {
      unfold runSt in *.
      eassumption.
    }

    Check multi_ev_eval.
    (*
multi_ev_eval
     : forall (t : AnnoTerm) (t' : Term) (n : nat) (tr : list Ev) (e e' : EvidenceC) (p p' : nat)
         (o o' : ev_store) (es e's : Evidence),
       t = snd (anno t' n) ->
       build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
       (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}) ->
       Ev_Shape e es -> eval (unanno t) p es = e's -> Ev_Shape e' e's
     *)
    
    apply multi_ev_eval with (t:=a) (t':=t'1) (n:=p') (tr:=H10) (e:=e) (e':=x) (p:=p) (p':= H11) (o:=o) (o':=H12) (es:=et).
                                                                                            
    rewrite Heqp0.
    reflexivity.
    simpl.
    eassumption.
    eassumption.
    simpl.

    rewrite H.
    reflexivity.
    Lemma evMappedSub : forall t p e m,
      evMapped (eval t p e) m ->
      evMapped e m.
    Proof.
    Admitted.

    eapply evMappedSub; eauto.
    unfold runSt.
    rewrite hi.
    assert (a2 = a_st).
    {
      admit.
    }
    rewrite H17.
    reflexivity.
    repeat break_let.
    
    
    repeat find_inversion.
    eassumption.













    


    
    unfold runSt.
    subst.
    rewrite hi.
    reflexivity.

    admit.
    rewrite H7.
    simpl.
    rewrite H.
    reflexivity.
    repeat break_let.
    rewrite Heqp2 in *.
    repeat find_inversion.
    assert (p = H11).
    {
      admit.
    }
    rewrite H.
    eassumption.
  -
    
    
   
    reflexivity.
    
    reflexivity.
    eassumption.
    unfold runSt.
    cbn.
    rewrite hi.
    reflexivity.
    cbn.
    simpl.
    repeat break_let.
    rewrite Heqp2 in *.
    repeat find_inversion.
    eassumption.
    unfold runSt.

    rewrite H13.
    
    rewrite hi.
    repeat find_inversion.
    rewrite H14.
    reflexivity.
    reflexivity.
    
    reflexivity.
    
    eassumption.
   
    reflexivity.
    
    
    
    
    apply H1.
    
    edestruct IHt'2.
    eassumption.

    eapply IHt'2.
    2 : {
      reflexivity.
    }
    2: { 
    
    
    
  *)  
    
      
      
      
      
      
(*
Lemma app_some'' : forall t t' p p' p'' tr o e' (app_comp: AM (VM unit)) app_comp_res a_st,
    t = snd (anno t' p') ->
    build_comp t {| st_ev:=mtc; st_trace:=[]; st_pl:=p; st_store:=[]|} =
    (Some tt, {| st_ev:=e'; st_trace:=tr; st_pl:=p''; st_store:=o|}) ->
    allMapped t p a_st ->
    app_comp = gen_appraisal_comp e' (eval t' p mt) ->
    app_comp_res = runSt a_st app_comp ->
    (*Ev_Shape e' (eval t' p mt) -> *)
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  assert (Ev_Shape e' (eval t' p mt)).
  eapply multi_ev_eval; eauto.
  rewrite H.
  erewrite announ'.
  reflexivity.
  generalize dependent t.
  generalize dependent p'.
  generalize dependent app_comp.
  generalize dependent app_comp_res.
  generalize dependent a_st.
  generalize dependent o.
  generalize dependent p''.
  generalize dependent tr.
  (*
  generalize dependent t'.
  generalize dependent p. *)
  induction H4; intros; subst.
  -
    cbv.
    eauto.
  -
    edestruct IHEv_Shape.
    reflexivity.
    reflexivity.
    reflexivity.
    admit.
    eassumption.
    
 
    unfold runSt in H.
    repeat break_let.
    simpl in *.
    subst.
    unfold runSt in *.
    monad_unfold.
    repeat break_let.
    assert (a_st = a).
    { admit. }
    rewrite H2 in *. clear H2.
    subst.
    rewrite Heqp0 in *. clear Heqp0.
    simpl in *.
    repeat find_inversion.
    subst.
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    edestruct H1.
    econstructor.
    admit.
    econstructor.
    reflexivity.
    inv H.
    rewrite H2 in *.
    monad_unfold.
    repeat find_inversion.
    eexists.
    simpl.
    eauto.
  -
    cbv.
    eexists.
    eauto.
  - cbv.
    eexists.
    eauto.
  - cbv.
    eexists.
    eauto.
  -
    edestruct IHEv_Shape1.
    reflexivity.
    reflexivity.
    reflexivity.
    admit.
    eassumption.
    edestruct IHEv_Shape2.
    reflexivity.
    reflexivity.
    reflexivity.
    admit.
    eassumption.
    unfold runSt.
    cbn.
    monad_unfold.
    unfold runSt in *.
    destruct (gen_appraisal_comp e1 e1t a_st) eqn:aa.
    simpl in *.
    destruct (gen_appraisal_comp e2 e2t a_st) eqn:bb.
    simpl in *.
    subst.
    repeat break_let.
    destruct a_st.
    destruct a.
    destruct a1.
    simpl.
    destruct a2.
    simpl in *.
    cbn in *.
    break_match.
    repeat find_inversion.
    eexists.
    eauto.
    repeat find_inversion.
    assert ({| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} =
            {| am_nonceMap := am_nonceMap0; am_nonceId := am_nonceId0; st_aspmap := st_aspmap0 |}).
    {
      admit.
    }
    rewrite H in *.
    congruence.
  -
    
    
    
    
    
    
      



    
    repeat break_match.
    +
      repeat find_inversion.
      eexists.
      simpl.
      eauto.
    + repeat find_inversion.
      destruct a_st.
      destruct a.
      simpl in *.
      assert (
          {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} =
          {| am_nonceMap := am_nonceMap0; am_nonceId := am_nonceId0; st_aspmap := st_aspmap0 |}
        ).
      {
        admit.
      }
      rewrite H1 in *. clear H1.
      rewrite Heqp0 in *.
      solve_by_inversion.
    +
      assert (a = a_st).
      {
        admit.
      }
      rewrite H1 in *. clear H1.
      rewrite Heqp0 in *.
      simpl in *.
      
      repeat find_inversion.
      subst.

      destruct a_st.
      destruct a.

       assert (
          {| am_nonceMap := am_nonceMap; am_nonceId := am_nonceId; st_aspmap := st_aspmap |} =
          {| am_nonceMap := am_nonceMap0; am_nonceId := am_nonceId0; st_aspmap := st_aspmap0 |}
        ).
      {
        admit.
      }
      rewrite H1 in *. clear H1.
      rewrite Heqp0 in *. clear Heqp0.
      simpl in *.
      repeat find_inversion.
      
      
      
      
      unfold gen_appraisal_comp in H
      edestruct H0.
      econstructor.
      econstructor.
      
    


    
    rewrite Heqp0 in *.
    
    inv H3.
    destruct t';
      try destruct a;
      try (cbv; eauto; tauto).
  -

    inv H3.
    destruct t';
      try destruct a;
      try (simpl in *; eauto; solve_by_inversion).
    + simpl in *.
      inv H5.
      monad_unfold.
      edestruct H0.
      econstructor.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      inv H.
      unfold am_get_app_asp.
      monad_unfold.
      repeat break_let.
      unfold runSt.
      monad_unfold.
      repeat break_let.
      rewrite H2 in *.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      inv H1.
      unfold gen_appraisal_comp in *.
      monad_unfold.
      repeat find_inversion.
      eexists.
      eauto.
    +



      
      simpl in *.
      repeat break_let.
      simpl in *.
      edestruct allMappedAt.
      apply H0.
      econstructor.
      inv H3.
      subst.
      repeat find_inversion.
      simpl in H3.
      
      rewrite <- H5 in *.
      invc H3.
      invc H7.
      unfold gen_appraisal_comp.
      monad_unfold.
      repeat break_let.
      simpl in *.
      unfold runSt.
      clear H2.
      edestruct H0.
      simpl.
      econstructor.
      econstructor.
      admit.
      econstructor.
      reflexivity.
      inv H.
      unfold am_get_app_asp.
      monad_unfold.
      rewrite H2.
      repeat break_let.
      
      econstructor.
      rewrite H7 in *.
      
      
      
    simpl in H5.
      
    subst.
    unfold gen_appraisal_comp.
    monad_unfold.
    unfold runSt.
    edestruct H0.
    
    simpl in H.
    cbv.
    eexists.
    eauto.
    + inv H.
    + inv H.
    + inv H.
    + inv H.
      destruct t'.
      destruct a.
      simpl in H.
      cbv.
      eauto.
      inv H2.
      inv H2.
      inv H2.
      inv H2.
      cbv.
      eauto.
      inv H2.
      cbv.
      eauto.
      cbv.
      eauto.
      cbv.
      eauto.
    + cbv.
      eauto.
    + cbv.
      eauto.
    +
      
      
      


          
      
      
      
      
    cbv.
    eexists.
    eauto.
  -
    subst.
    unfold gen_appraisal_comp.
    monad_unfold.
    unfold runSt.
    eapply IHEv_Shape.
    reflexivity.
    unfold gen_appraisal_comp at 1.
    monad_unfold.
    unfold runSt.
    unfold am_get_app_asp.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    cbv
    
    
  -
    
  induction t; intros.
  -
    destruct a.
    +
      annogo.
      inv H3.
      cbv.
      eexists.
      eauto.
    + annogo.
      inv H3.
      cbn.
      monad_unfold.
      edestruct H0.
      econstructor.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      inv H1.
      unfold am_get_app_asp.
      monad_unfold.
      repeat break_let.
      rewrite H2 in *.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      inv H4.
      cbn in *.
      monad_unfold.
      repeat find_inversion.
      simpl in *.
      cbn.
      monad_unfold.
      eexists.
      eauto.
    +
       annogo.
      inv H3.
      cbv.
      eexists.
      eauto.
    +
       annogo.
      inv H3.
      cbv.
      eexists.
      eauto.
  -
    destruct r.
    Check afff.
    assert (exists t'' n', t = snd (anno t'' n')).
    {
      eapply afff.
      exact 0.
      symmetry.
      eassumption.
    }
      
    destruct_conjs.
    simpl.
    subst.

    edestruct allMappedAt.
   ++
     apply H0.
   ++
     

    edestruct IHt.
    eassumption.
    
    
      
      
      
      
      cbv.
      eexists.
      eauto.
      
      
    
  
Admitted.
 *)

Print allMapped.


Lemma app_some : forall t t' p' (vm_st':vm_st) (app_comp: AM vm_st) app_comp_res a_st,
    t = snd (anno t' p') ->
    build_comp t empty_vmst = (Some tt, vm_st') ->
    allMapped t 0 mt a_st ->
    app_comp = exec_app_comp_t t' 0 p' empty_vmst ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  vmsts.
  unfold empty_vmst in *.
  edestruct app_some'' with (t:=t) (t':=t') (p':=p') (e':=st_ev).
  eassumption.
  eassumption.
  econstructor.
  eassumption.
  reflexivity.
  reflexivity.
  cbv.
  eauto.
  reflexivity.
  reflexivity.
  subst.

  (*
  eapply multi_ev_eval.
  eassumption.
  apply H0.
  econstructor.
  rewrite H.
  erewrite announ'.
  reflexivity.
  subst. *)

  
  unfold exec_app_comp_t.
  unfold exec_app_comp.
  monad_unfold.
  unfold build_app_comp.
  monad_unfold.
  unfold runSt.
  unfold run_vm.
  monad_unfold.
  rewrite H0.
  simpl.
  erewrite announ'.
  unfold runSt in *.
  repeat break_match; try solve_by_inversion.
  repeat find_inversion.
  eexists.
  simpl.
  eauto.
Defined.




                                
  

Lemma app_some : forall t t' p p' vm_st' app_comp app_comp_res a_st,
    t = snd (anno t' p') ->
    build_comp t empty_vmst = (Some tt, vm_st') ->
    allMapped t p a_st ->
    app_comp = exec_app_comp_t t' p p' empty_vmst ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
Proof.
  induction t; intros; subst.
  -

    destruct a.
    + unfold exec_app_comp_t.
      unfold exec_app_comp.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      simpl in *.
      repeat find_inversion.
      unfold runSt.
      rewrite <- H.
      simpl.
      cbn.
      unfold build_app_comp.
      monad_unfold.



      repeat break_match; try solve_by_inversion.
      eexists.
      simpl.
      reflexivity.
      repeat find_inversion.
      unfold empty_vmst in *.
      repeat find_inversion.
      unfold gen_appraisal_comp in *.
      monad_unfold.
      solve_by_inversion.
    +
      vmsts.
      simpl in *.
      monad_unfold.
      repeat find_inversion.
      unfold runSt.
      cbn.
      unfold exec_app_comp_t.
      unfold exec_app_comp.
      monad_unfold.
      unfold build_app_comp.
      monad_unfold.
      monad_unfold.
      unfold allMapped in H1.
      repeat break_match; try solve_by_inversion.
      repeat break_let.
      repeat find_inversion.
      unfold runSt.
      repeat break_let.
      eexists. simpl.
      eauto.
      repeat find_inversion.
      rewrite <- H in *.
      simpl in Heqp1.
      monad_unfold.
      edestruct H1.
      econstructor.
      econstructor.
      reflexivity.
      econstructor.
      reflexivity.
      inv H0.
      unfold am_get_app_asp in *.
      monad_unfold.
      repeat break_let.
      rewrite H2 in *.
      repeat break_match;
        try solve_by_inversion.
      ++
        repeat break_let.
        cbn in *.
        repeat find_inversion.
      ++
        repeat find_inversion.
        clear H0.
        unfold empty_vmst in *.
        repeat find_inversion.
        unfold gen_appraisal_comp in *.
        monad_unfold.
        solve_by_inversion.
      ++
        repeat find_inversion.
    +
      vmsts.
      unfold empty_vmst in *.
      simpl in *.
      monad_unfold.
      repeat find_inversion.
      unfold runSt.
      repeat break_let.
      simpl in *.
      cbn.
      repeat find_inversion.
      unfold exec_app_comp_t.
      rewrite <- H in *.
      cbn.
      eexists.
      reflexivity.
    +
       vmsts.
      unfold empty_vmst in *.
      simpl in *.
      monad_unfold.
      repeat find_inversion.
      unfold runSt.
      repeat break_let.
      simpl in *.
      cbn.
      repeat find_inversion.
      unfold exec_app_comp_t.
      rewrite <- H in *.
      cbn.
      eexists.
      reflexivity.
  -
    unfold exec_app_comp_t.
    unfold exec_app_comp.
    Lemma build_at : forall r n t st st',
      build_comp (aatt r n t) st = (Some tt,st') ->
      build_comp t st = (Some tt, st').
    Proof.
    Admitted.
    
    assert (build_comp t empty_vmst = (Some tt, vm_st')).
    eapply build_at; eauto.
    
    rewrite <- H.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    vmsts.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    repeat find_inversion.
    unfold runSt.
    repeat break_let.
    repeat break_match.
    repeat find_inversion.
    ++ simpl. eauto.
    ++ repeat find_inversion.


       destruct afff with (t':=t') (r:=n0) (s:=n1) (x:=n) (t:=t) (n0:=p').
       exact p'.
       symmetry.
       eassumption.
       destruct_conjs.
       edestruct IHt.
       eassumption.
       eassumption.
       eapply allMappedAt; eauto.
       reflexivity.
       reflexivity.
       Print build_app_comp.
       unfold build_app_comp in *.
       monad_unfold.
       unfold run_vm in Heqp0.
       monad_unfold.
       monad_unfold.
       repeat break_let.
       unfold get_store_at in *.
       monad_unfold.
       dohtac.
       repeat find_inversion.
       simpl in *.
       repeat break_match; try solve_by_inversion.
       repeat find_inversion.
       unfold exec_app_comp_t in *.
       unfold exec_app_comp in *.
       monad_unfold.
       rewrite H2 in *.
       repeat break_match; try solve_by_inversion.
       rewrite <- H2 in *.
       unfold build_app_comp in *.
       monad_unfold.
       unfold runSt in *.

       assert ((toRemote (unanno (snd (anno x H0))) st_ev) =
               (StVM.st_ev
                  (run_vm (snd (anno x H0))
                     {|
                     st_ev := st_ev;
                     st_trace := st_trace1;
                     st_pl := st_pl;
                     st_store := st_store0 |}))).
       {
         admit. (* TODO: axiom? *)
       }
       rewrite H3 in *.
       unfold run_vm in *.
       monad_unfold.
       rewrite H2 in *.
       simpl in *.
       rewrite Heqp1 in *.
       solve_by_inversion.
  -
    destruct vm_st'.
    unfold empty_vmst in *.
    assert (Ev_Shape st_ev (Term.eval (unanno (alseq r t1 t2)) 0 mt)).
    eapply multi_ev_eval.
    eassumption.
    eassumption.
    econstructor.
    reflexivity.
    inv H2
    
      

       
               
       
      
    unfold snd in *.
    assert (exists vvss, (build_comp a empty_vmst) = (Some tt, vvss)).
    {
      admit.
    }
    destruct_conjs.
    
    cbn in *.
    repeat break_let.
    monad_unfold.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    repeat find_inversion.
    break_match.
    +
      repeat break_let.
      simpl.
      eauto.

      (*
      subst.
      unfold build_app_comp in *.
      monad_unfold.
      simpl in *.
      cbn in *.
      unfold run_vm_fresh in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let.
      dohtac.
      repeat find_inversion.
      simpl in *.
      destruct o; try solve_by_inversion.
      repeat find_inversion.
      edestruct IHt.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eapply allMappedAt; eauto.
      reflexivity.
      reflexivity.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      rewrite Heqp0 in *.
      simpl in *.
      unfold runSt in *.
      Print gen_appraisal_comp.
      Print build_app_comp.
      unfold build_app_comp in *.
      monad_unfold.
      assert (
          (toRemote (unanno a) n mtc) =
          (st_ev (run_vm_fresh a))).
      {
        admit.
      }
      rewrite <- H3 in *.
      rewrite Heqp2 in *.
      repeat find_inversion.
      simpl in *.
      rewrite Heqp8 in *.
      simpl in *.
      eexists.
      reflexivity. *)
    +
      unfold build_app_comp in *.
      monad_unfold.
      unfold run_vm_fresh in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      unfold get_store_at in *.
      monad_unfold.
      dohtac.
      repeat find_inversion.
      simpl in *.
      destruct o0; try solve_by_inversion.
      repeat find_inversion.
      edestruct IHt.
      rewrite Heqp0.
      eassumption.
      rewrite Heqp0.
      eapply allMappedAt; eauto.
      reflexivity.
      reflexivity.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      unfold runSt in *.
      rewrite Heqp0 in *.
      simpl in *.
      unfold build_app_comp in *.
      monad_unfold.

      assert ((toRemote (unanno a) n mtc) =
              (st_ev (run_vm_fresh a))).
      {
        admit.
      }
      rewrite <- H3 in *.
      rewrite Heqp2 in *.
      simpl in *.
      congruence.
  -
    destruct ((snd (anno (lseq t1 t2) p'))) eqn:hi;
      try (inv hi;
           repeat break_let;
           simpl in *;
           solve_by_inversion).




    unfold empty_vmst in *.
    vmsts.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    repeat break_let.

    unfold exec_app_comp_t.
    unfold exec_app_comp.
    monad_unfold.
    unfold runSt.
    repeat break_let.
    simpl in *.

    destruct o; try solve_by_inversion.
    repeat find_inversion.
    rewrite Heqp6 in *.
    repeat find_inversion.

    destruct o1.
    + admit.
    +
      

    assert ((allMapped (alseq (p', n0) a1 a2) p a_st) -> False).
    admit.
    tauto.
















    
    repeat find_inversion.
    unfold build_app_comp in *.
    monad_unfold.
    unfold run_vm_fresh in *.
    unfold run_vm in *.
    monad_unfold.
    simpl in *.
    monad_unfold.
    unfold empty_vmst in *.
    rewrite Heqp2 in *.
    monad_unfold.
    simpl in *.
    repeat break_let.
    simpl in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    rewrite Heqp6 in *.
    repeat find_inversion.
    repeat break_let.

    repeat break_match;
      try solve_by_inversion.
    +
      repeat find_inversion.
      destruct v0.
      simpl.
      eexists. eauto.
    +
      repeat find_inversion.
      destruct v.
      simpl in *.
      destruct o0.
      dunit.
      repeat find_inversion.
      
      eapply fals.
      rewrite Heqp6. reflexivity.
      
      

    unfold gen_appraisal_comp in *
                                 




    
    rewrite <- Heqp6 in *.

    assert ( (let (_, y) := anno t2 p' in y) =  (let (_, y) := anno t2 p' in y)
    
      
      
      
      unfold 
      
      
      unfold gen_appraisal_comp in *
      eapply IHt.
      unfold gen_appraisal_comp in *
      
    
    
    
    
      
    
    
  

Lemma app_correct :
  forall t app_comp app_comp_res app_comp_st tr_app_comp ev p p' a_st st',

    build_comp (snd (anno t p')) empty_vmst = (Some tt, st') ->
    app_comp = exec_app_comp_t t p p'  (* AM vm_st *) ->
    app_comp_res = runSt a_st app_comp (* ((option vm_st) * AM_St) *)  -> 
    app_comp_st = fromOpt (fst app_comp_res) empty_vmst (* vm_st *)  ->
    tr_app_comp = st_trace app_comp_st ->
                      
    measEvent (snd (anno t p')) p ev ->
    allMapped (snd (anno t p')) p a_st ->
    exists ev', In ev' tr_app_comp /\ appEvent ev a_st ev'.
Proof.
  induction t; intros; subst.
  -
    destruct a;
      try (invc H4;
           invc H1;
           solve_by_inversion).
    +
      inv H4.
      inv H1.
      inv H0.
      simpl in *.
      repeat find_inversion.
         
      simpl in *.
      monad_unfold.
      unfold allMapped in *.
      edestruct H5.
      eassumption.
      reflexivity.
      unfold am_get_app_asp.
      inv H2.
      unfold exec_app_comp_t.
      unfold exec_app_comp.
      unfold build_app_comp.
      monad_unfold.
      monad_unfold.
      unfold runSt.
      unfold am_get_app_asp.
      monad_unfold.
      repeat break_let.
      rewrite H3 in *.
      simpl in *.
      repeat find_inversion.
      simpl in *.
      Print appEvent.
      eexists.
      split.
      eauto.
      destruct a.
      Print appEvent.
      econstructor.
      eauto.
  -
    inv H4.
    inv H1.
    cbn in *.
    repeat break_let.
    unfold snd in *.
    assert ((build_comp a empty_vmst) = (Some tt, st')).
    {
      admit.
    }
    
    simpl in *.
    inv H0.

    assert (allMapped a n a_st).
    eapply allMappedAt; eauto.
        
    unfold allMapped in H5.
    edestruct H5.
    eassumption.
    reflexivity.
    inv H6.
    
    edestruct IHt.
    rewrite Heqp1.
    eassumption.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    eapply measEventAt'.
    assert ((aatt (p',S n1) n a) = (snd (anno (att n t) p'))) as HH.
    {
      cbn. repeat break_let.
      simpl.
      congruence.
    }
    rewrite <- HH. clear HH.
    eassumption.
    rewrite Heqp1.
    simpl.
    eassumption.

    exists x0.
    unfold exec_app_comp_t in *.
    unfold exec_app_comp in *.
    monad_unfold.
    rewrite Heqp1 in *.
    simpl in *.
    unfold runSt in *.
    simpl in *.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    repeat find_inversion.
    repeat break_match; try solve_by_inversion.
    +
      repeat find_inversion.
      simpl in *.
      repeat find_inversion.
      cbn in *.
      unfold build_app_comp in *.
      monad_unfold.
      cbn in *.

      unfold run_vm_fresh in *.
      unfold run_vm in Heqp7.
      unfold execSt in Heqp7.
      cbn in Heqp7.
      repeat break_let.
      repeat find_inversion.
      monad_unfold.
      repeat find_inversion.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let.
      dohtac.
      repeat find_inversion.
      simpl in *.
      assert ((st_ev (run_vm a empty_vmst)) = (toRemote (unanno a) n mtc)).
      {
        admit. (* TODO: make this an axiom? *)
      }
      rewrite H in *.
      subst.
      rewrite Heqp6 in *.
      repeat find_inversion.
      repeat break_match; try solve_by_inversion.
      repeat find_inversion.
      eassumption.
    + simpl in *.
      tauto.
    + simpl in *.
      repeat find_inversion.
      unfold build_app_comp in *.
      monad_unfold.
      unfold run_vm_fresh in *.
      cbn in *.
      unfold run_vm in Heqp7.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      repeat find_inversion.
      simpl in *.
      unfold get_store_at in *. monad_unfold. repeat break_let.
      dohtac.
      repeat find_inversion.
      simpl in *.

       assert ((st_ev (run_vm a empty_vmst)) = (toRemote (unanno a) n mtc)).
      {
        admit. (* TODO: make this an axiom? *)
      }
      rewrite H in *.
      rewrite Heqp9 in *.
      repeat find_inversion.
      repeat break_match; solve_by_inversion.
  -
    invc H4.
    invc H1.
    invc H0; repeat break_let; simpl in *; try solve_by_inversion; invc H1.
    +
    unfold exec_app_comp_t.
    unfold exec_app_comp.
    monad_unfold.
    simpl in *.
    repeat break_let.
    unfold snd in *.
    (*build_comp (alseq (p', n3) a1 a2) empty_vmst = (Some tt, st')*)
    Print build_app_comp.
    unfold runSt.
    unfold build_app_comp.
    monad_unfold.
    unfold run_vm_fresh.
    unfold run_vm.
    unfold execSt.
    cbn.
    rewrite H.
    simpl in *.
    unfold runSt.
    simpl in *.
    repeat break_match; try solve_by_inversion; repeat find_inversion.
    ++
      simpl in *.
      unfold build_app_comp in *.
      monad_unfold.
      repeat find_inversion.
      unfold run_vm_fresh in *.
      unfold run_vm in *.
      monad_unfold.
      monad_unfold.
      simpl in *.
      repeat break_match; try solve_by_inversion.
      +++ repeat find_inversion.
          simpl in *.
          repeat find_inversion.
          edestruct IHt1; try reflexivity.
          rewrite Heqp2.
          simpl.
          dunit.
          eassumption.
          econstructor.
          rewrite Heqp2.
          eassumption.
          simpl.
          econstructor.
          simpl.
          rewrite Heqp2.
          Lemma allMappedL : forall r t1 t2 p st,
            allMapped (alseq r t1 t2) p st ->
            allMapped t1 p st.
          Proof.
          Admitted.

          eapply allMappedL; eauto.
          exists x.
          dunit.
          destruct_conjs.
          unfold exec_app_comp_t in *.
          unfold exec_app_comp in *.
          monad_unfold.
          unfold runSt in *.
          rewrite Heqp2 in *.
          simpl in *.
          repeat break_match; try solve_by_inversion.
          simpl in *.
          repeat find_inversion.
          destruct o; try solve_by_inversion.
          repeat find_inversion.
          admit.
    ++
      admit.
    +
      repeat break_let; simpl in *.
      repeat find_inversion.
      admit.
  -
    
      
      
      +++ repeat find_inversion.
          simpl in *.
          
          unfold gen_appraisal_comp in *
    
    invc H0.
    
      
      
      
      
      


















    
    unfold allMapped.
    intros; subst.
      
    unfold anno in Heqp1
    cbn in H3.
    break_let.
    simpl in H3.
    inv H3.
    inv H2.
    cbn in H.
    break_let.
    simpl in H.
    clear H2.
    clear H0.
    

    Check measEventAt'.
    unfold annotated.
    Check measEventAt'.
    cbn in H4.
    break_let.
    simpl in H4.
    eapply measEventAt'.
    cbn.
    break_let.
    eassumption.

    
    cbn in H4.
    repeat break_let.
    simpl in H4.
    simpl.
    
    repeat find_inversion.
    unfold allMapped in H4.
    inv H0.
    edestruct H4.
    apply H3.
    reflexivity.

    unfold allMapped.
    intros.
    subst.
    cbn in H3.
    break_let.
    simpl in H3.

    exists x.
    
    admit.
    inv H1
    apply H1.
    eassumption.
    intros.
    subst.
    

    

    



    eapply measEventAt.
    eassumption.
    destruct_conjs.
    monad_unfold.
    unfold exec_app_comp_t.
    unfold exec_app_comp.
    monad_unfold.
    unfold runSt.
    break_match.
    destruct o.
    +
      simpl.
      destruct ast.
      monad_unfold.
      unfold runSt in *.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      cbn in *.
      repeat break_let.
      simpl in *.
      unfold build_app_comp in Heqp.
      monad_unfold.
      unfold run_vm_fresh in Heqp.
      monad_unfold.
      unfold run_vm in Heqp.
      monad_unfold.
      monad_unfold.
      repeat break_let.
      repeat find_inversion.
      simpl in *.

      Require Import MonadVMFacts.
      vmsts.
      simpl in *.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let.
      dohtac.
      repeat find_inversion.
      repeat break_match;
        repeat find_inversion.
      ++  vmsts.
          vmsts.
          inv H2.
          unfold build_app_comp in *.
          monad_unfold.
          unfold run_vm_fresh in Heqp0.
          unfold run_vm in *.
          monad_unfold.
          Print unanno.



          rewrite announ in *.

          Print build_comp.
          repeat break_match;
            try solve_by_inversion.
          repeat find_inversion.

          unfold runSt in *.



          exists (umeas m q i' (args ++ [n0])).
          split.

          eapply atgentrace.
          apply Heqp2.
          apply Heqp1.
          eassumption.
          eauto.
      ++
        unfold build_app_comp in *.
        monad_unfold.
        repeat break_match;
          try solve_by_inversion.
    +
      inv H3.
      inv H2.
      simpl.
      unfold allMapped in *.
      edestruct H4 with (st:=ast).
      eassumption.
      reflexivity.
      repeat find_inversion.
      unfold runSt in *.
      monad_unfold.
      unfold exec_app_comp_t in *.
      unfold exec_app_comp in *.
      monad_unfold.
      repeat break_match;
        try solve_by_inversion.
      simpl in *.
      unfold build_app_comp in *.
      monad_unfold.
      repeat break_match;
        try solve_by_inversion.
      ++ rewrite announ in *.
         repeat find_inversion.
         unfold run_vm_fresh in *.
         unfold run_vm in *.
         monad_unfold.
         destruct ast.
         simpl in *.



         exfalso.
         eapply fifi; eauto.
      
             
  - 
    
          
          
              
              
   (*           
              
              unfold annotated in *.
              rewrite <- IHt.
              unfold anno in Heqp
              
              simpl.
              
            intros.
            unfold annotated.
            induction 
            -
              unfold anno. simpl. reflexivity.
            - simpl. repeat break_let. simpl. unfold unanno
              
          Admitted.
          

            
          unfold gen_appraisal_comp in *
          inv H.
          invc H7.
          invc H7.
          invc H8.
          +++
            unfold runSt in H1.
            unfold build_app_comp in *.
            monad_unfold.

            destruct v.
              simpl. vmsts.
              simpl.
              unfold gen_appraisal_comp in Heqp2.

            
          unfold gen_appraisal_comp in Heqp2
    
    
      
           
 
         unfold bind.
         unfold run_vm_fresh.
         unfold run_vm.
         unfold execSt.
         unfold eval.
         unfold annotated.
         unfold anno.
         simpl.
         unfold bind.
         unfold am_get_app_asp.
         unfold bind.
         unfold gets.
         unfold bind.
         unfold runSt.
         unfold get.
         repeat break_let.
         repeat find_inversion.
         repeat break_match.
                     
         monad_unfold.
         unfold build_app_comp.
         monad_unfold.
         monad_unfold.
         unfold am_get_app_asp.
         monad_unfold.
         repeat break_let.
         unfold map_get
         














      
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
    Print measEvent.
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

*)
  
  
  

