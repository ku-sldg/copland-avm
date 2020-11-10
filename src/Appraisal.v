Require Import GenStMonad MonadVM MonadAM ConcreteEvidence MonadVMFacts.
Require Import StAM VM_IO_Axioms Maps VmSemantics Event_system Term_system.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

Definition extractSig (e:EvidenceC) : VM (BS * EvidenceC) :=
  match e with
  | ggc bs e' => ret (bs, e')
  | _ => failm
  end.

(*
Definition extractHsh (e:EvidenceC) : VM (BS * EvidenceC) :=
  match e with
  | hhc bs e' => ret (bs, e')
  | _ => failm
  end. *)

(*
Definition extractComp (e:EvidenceC) : VM (EvidenceC * EvidenceC) :=
  match e with
  | ssc e1 e2 => ret (e1,e2)
  | ppc e1 e2 => ret (e1,e2)
  | _ => failm
  end.
 *)

Definition am_get_app_asp (p:Plc) (i:ASP_ID) : AM ASP_ID :=
  m <- gets st_aspmap ;;
  let maybeId := map_get m (p,i) in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

Definition am_get_sig_asp (p:Plc) : AM ASP_ID :=
  m <- gets st_sigmap ;;
  let maybeId := map_get m p in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.

Definition checkSig (x:nat) (i:ASP_ID) (e':EvidenceC) (sig:BS) : VM BS :=
  invokeUSM x i ([encodeEv e'] ++ [sig] (* ++ args*) ) mtc.

Definition extractUev (e:EvidenceC) : VM (BS * EvidenceC) :=
  match e with
  | uuc i bs e' => ret (bs,e')
  | _ => failm
  end.

Definition checkUSM (x:nat) (i:ASP_ID) (l:list Arg) (bs:BS) : VM BS :=
  invokeUSM x i ([bs] ++ l) mtc.


Fixpoint build_app_comp (t:AnnoTerm) (p:Plc) : AM (VM (EvidenceC -> EvidenceC)) :=
  match t with
  | alseq (n,n') t' (aasp r' SIG) =>
    app_id <- am_get_sig_asp p ;;
    d <- build_app_comp t' p ;;
    let c :=
        (
          e <- get_ev ;;
          pr <- extractSig e ;;
          let '(bs,e') := pr in
          res <- checkSig n app_id e' bs ;;
          put_ev e' ;;
          e_res <- d ;;
          ret (fun x => ggc res (e_res x))) in
    ret c   

  | alseq (n,n') t1 t2 =>
    c <- build_app_comp t1 p ;;
    d <- build_app_comp t2 p ;;
    let cc :=
        (
          g <- d ;;
          f <- c ;;
          ret (fun x => g (f x))
        ) in
    ret cc

        
  | aasp (n,n') (ASPC i args) =>
    app_id <- am_get_app_asp p i ;;
    let c :=
        (
          e <- get_ev ;;
          pr <- extractUev e ;;
          let '(bs,e') := pr in
          res <- checkUSM n app_id args bs ;;
          put_ev e' ;;
          ret (fun x => (uuc n res x) )) in
    ret c

  | aasp (n,n') (SIG) =>
    app_id <- am_get_sig_asp p ;;
    let c :=
        e <- get_ev ;;
        pr <- extractSig e ;;
        let '(bs,e') := pr in
        res <- checkSig n app_id e' bs ;;
        put_ev e' ;;
        ret (fun x => ggc res x) in
    
    ret c

  | aasp (n,n') (CPY) =>
    let c :=
        ret (fun x => x) in    
    ret c
        
  (*
  | aasp (n,n') (HSH) =>
   (* app_id <- am_get_sig_asp p ;; *) (* TODO: get_hsh_asp impl *) 
    let c :=
        e <- get_ev ;;
        pr <- extractHsh e ;;
        let '(bs,e') := pr in
        (*
        res <- checkSig n app_id ([encodeEv e'] ++ [bs] (* ++ args*) ) ;;
        put_ev e' ;; (* TODO: does this have any effect? *) 
        ret (ggc res e') *)
        put_ev e' ;;
        ret (fun x => hhc 0 x) in
        
    ret c     
   *)
        
  | aatt r q t' =>
    build_app_comp t' q
                   (*| _ => ret (ret (fun _ => mtc)) *)
  end.

(*
  e <- get_ev ;;
  pr <- extractComp e ;;
  let '(e1,e2) := pr in
  put_ev e1 ;;
  e1_res <- c ;;
  put_ev e2 ;;
  e2_res <- d ;;
  ret (ssc e1_res e2_res)
 *)


Inductive evMapped : Evidence -> AM_St -> Prop :=
| evMappedMt : forall m, evMapped mt m
| evMappedU : forall p i args e' m st,
    m = st_aspmap st ->
    evMapped e' st -> 
    (exists j, bound_to m (p,i) j) -> 
    evMapped (uu i args p e') st
| evMappedG : forall e' m p st,
    m = st_sigmap st ->
    evMapped e' st ->
    (exists j, bound_to m p j) ->
    evMapped (gg p e') st
(*| evMappedH : forall e' p st,
    (*m = st_sigmap st -> *)
    evMapped e' st ->
    evMapped (hh p e') st    
| evMappedN : forall e' m nid st,
    m = st_aspmap st ->
    evMapped e' st ->
    evMapped (nn nid e') st 
| evMappedS : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (ss e1 e2) st
| evMappedP : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (pp e1 e2) st 
 *).


Inductive allMapped : AnnoTerm -> AM_St -> Plc -> Evidence -> Prop :=
| allMapped_cpy : forall r p st e,
    (*m = st_aspmap st -> *)
    (*p = am_pl st -> *)
    evMapped e st ->
    allMapped (aasp r (CPY)) st p e
| allMapped_asp : forall m st p i r args e,
    (*p = am_pl st -> *)
    evMapped e st ->
    m = st_aspmap st ->
    (exists j, bound_to m (p,i) j) ->
    allMapped (aasp r (ASPC i args)) st p e
| allMapped_sig : forall r p st m e,
    evMapped e st ->
    (*p = am_pl st -> *)
    m = st_sigmap st ->
    (exists j, bound_to m p j) ->
    allMapped (aasp r (SIG)) st p e
(*| allMapped_hsh : forall r p st e,
    evMapped e st ->
    (*p = am_pl st -> *)
    allMapped (aasp r (HSH)) st p e *)
| allMapped_at : forall t' p q r st e m x y z z',
    m = st_aspmap st ->
    (*evMapped e m -> *) (* TODO: need this? *)
    st = (mkAM_St x y z z') ->
    allMapped t' (mkAM_St x y z z') q e ->
    allMapped (aatt r q t') st p e
| allMapped_lseq : forall t1 t2 p st r e,
    (* m = st_aspmap st ->
       evMapped e m -> *)  (* TODO: need this? *)
    (*p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p mt (*(eval (unanno t1) p e)*) -> (* TODO: is mt ok here? *)
    allMapped (alseq r t1 t2) st p e
(*| allMapped_bseq_nn : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p mt ->
    allMapped (abseq r (NONE,NONE) t1 t2) st p e
| allMapped_bseq_na : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p e ->
    allMapped (abseq r (NONE,ALL) t1 t2) st p e
| allMapped_bseq_an : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p mt ->
    allMapped (abseq r (ALL,NONE) t1 t2) st p e
| allMapped_bseq_aa : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p e ->
    allMapped (abseq r (ALL,ALL) t1 t2) st p e
| allMapped_bpar_nn : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p mt ->
    allMapped (abpar r (NONE,NONE) t1 t2) st p e
| allMapped_bpar_na : forall t1 t2 p st e r,
    (*p = am_pl st -> *)
    allMapped t1 st p mt ->
    allMapped t2 st p e ->
    allMapped (abpar r (NONE,ALL) t1 t2) st p e
| allMapped_bpar_an : forall t1 t2 p st e r,
   (* p = am_pl st -> *)
    allMapped t1 st p e ->
    allMapped t2 st p mt ->
    allMapped (abpar r (ALL,NONE) t1 t2) st p e
| allMapped_bpar_aa : forall t1 t2 p st e r,
    (*p = am_pl st ->*)
    allMapped t1 st p e ->
    allMapped t2 st p e ->
    allMapped (abpar r (ALL,ALL) t1 t2) st p e*).

(*
Definition allMapped (t:AnnoTerm) (a_st:AM_St) (p:Plc) (e:Evidence) : Prop :=
  evMapped (eval (unanno t) p e) a_st.
 *)

Ltac debound :=
  match goal with
  | [H: bound_to _ _ _ |- _] => invc H
  end.

Ltac evMappedFacts :=
  match goal with
  | [H: evMapped (uu _ _ _ _) _ |- _] => invc H
  | [H: evMapped (gg _ _) _ |- _] => invc H
  (* 
  | [H: evMapped (hh _ _) _ |- _] => invc H 
  | [H: evMapped (nn _ _) _ |- _] => invc H
  | [H: evMapped (ss _ _) _ |- _] => invc H
  | [H: evMapped (pp _ _) _ |- _] => invc H  
   *)
  end;
  destruct_conjs;
  try debound.

Ltac allMappedFacts := 
  match goal with
  | [H: allMapped (aasp _ _) _ _ _ |- _] => invc H
  | [H: allMapped (aatt _ _ _) _ _ _ |- _] => invc H
  | [H: allMapped (alseq _ _ _) _ _ _ |- _] => invc H
  (* 
  | [H: allMapped (abseq _ _ _ _) _ _ _ |- _] => invc H
  | [H: allMapped (abpar _ _ _ _) _ _ _ |- _] => invc H 
   *)
  end;
  destruct_conjs.



Lemma allMappedAt : forall r n a p st e,
    allMapped (aatt r n a) st p e ->
    allMapped a st n e.
Proof.
  intros.
  allMappedFacts.
  df.
  eauto.
Defined.

Ltac df :=
  repeat (
      cbn in *;
      unfold runSt in *;
      repeat break_let;
      repeat (monad_unfold; cbn in *; find_inversion);
      monad_unfold;
      repeat dunit;
      unfold snd in * ).

Ltac dosome :=
  repeat (
      match goal with
      | [H: match ?o with
            | Some _ => _
            | _ => _
            end
            =
            (Some _, _) |- _] =>
        destruct o; try solve_by_inversion
      end; df).

Ltac tacc H :=
  (symmetry;
   erewrite <- pl_immut in *;
   rewrite H;
   eauto ).

Ltac ff := repeat break_match; try solve_by_inversion; df.

Ltac dosome_eq y :=
  match goal with
  | [H: match ?x with _ => _ end = (Some _, _)  |- _] =>
    destruct x eqn:y; try solve_by_inversion
  end.
Ltac do_pair :=
  match goal with
  | [H: (_,_) = (Some _,_) |- _] => invc H
  | [H: (Some _,_) = (_,_) |- _] => invc H
  end.

Ltac amsts :=
  repeat match goal with
         | H:vm_st |- _ => destruct H
         end.

Ltac dosome_eqj :=
  let y := fresh in 
  match goal with
  | [H: match ?x with _ => _ end = (Some _, _)  |- _] =>
    destruct x eqn:y; try solve_by_inversion
  end.

Ltac dosome'' :=
  match goal with
  | [H: (_,_) = (Some _, _) |- _] => invc H
  end.

Ltac domap :=
  let n := fresh in
  match goal with
  | [H: match ?X with _ => _ end _ = (Some _, _) |- _] =>
    destruct X eqn:n; try solve_by_inversion
  end.


Ltac doit' := repeat dosome_eqj;
              repeat break_let;
              repeat do_pair;
              repeat break_let;
              repeat do_pair;
              repeat dosome''.

Ltac doit := repeat doit'.



(*
  Ltac map_get_subst :=
  match goal with
  | [H: map_get ?A ?B = _,
  H2: context[map_get ?A ?B] |- _] =>
  rewrite H in *; clear H
  end.
 *)



Ltac subst' :=
  match goal with
  | [H: ?A = _,
        H2: context[?A] |- _] =>
    rewrite H in *; clear H
  | [H: ?A = _ |- context[?A]] =>
    rewrite H in *; clear H
  end.

Ltac evShapeFacts :=
  match goal with
  | [H: Ev_Shape mtc _ |- _] => invc H
  | [H: Ev_Shape _ mt |- _] => invc H
  | [H: Ev_Shape (uuc _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (uu _ _ _ _) |- _] => invc H
  | [H: Ev_Shape (ggc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (gg _ _) |- _] => invc H
  (*
  | [H: Ev_Shape (hhc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (hh _ _) |- _] => invc H
  | [H: Ev_Shape (nnc _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (nn _ _) |- _] => invc H
  | [H: Ev_Shape (ssc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (ss _ _) |- _] => invc H
  | [H: Ev_Shape (ppc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (pp _ _) |- _] => invc H 
   *)
  end.

Ltac haaa :=
  let x:= fresh in
  match goal with
  | [H: context[match ?ee with | Some _ => _ | _ => _ end] |- _] =>
    destruct ee eqn:x;
    try solve_by_inversion
  end; df; eauto.

Ltac stt :=
  cbn in *;
  monad_unfold;
  try solve_by_inversion;
  repeat break_let;
  dosome;
  try haaa.

Ltac subst'' :=
  match goal with
  | H:?A = _, H2:context [ ?A ] |- _ => rewrite H in *
  | H:?A = _ |- context [ ?A ] => rewrite H in *
  end.

Lemma ba_const : forall a a_st a_st' o p,
    build_app_comp a p a_st = (o, a_st') ->
    a_st = a_st'.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    destruct a;
      repeat (ff; eauto).
  -
    eauto.
  (*
    edestruct IHa.
    eassumption.
    destruct_conjs.
    simpl in *.
    subst.
    tauto. *)
  -
    
    df.
    subst.
    destruct a2.
    +
      destruct a;
        repeat (ff;eauto).
      
    + (* aatt case *)
      doit.
      specialize IHa1 with (a_st:=a_st) (a_st':=a) (o:=o0) (p:=p).
      concludes.
      destruct_conjs.
      specialize IHa2 with (a_st := a) (a_st':=a0) (o:=o1) (p:=p).
      concludes.
      subst.
      
      ff; eauto.

    + (* alseq case *)

      doit.
      specialize IHa1 with (a_st:=a_st) (a_st':=a) (o:=o0) (p:=p).
      concludes.
      destruct_conjs.
      specialize IHa2 with (a_st := a) (a_st':=a0) (o:=o1) (p:=p).
      concludes.
      subst.
      ff; eauto.

(*
    +
    destruct (build_app_comp a1 p a_st) eqn:hey;
         try solve_by_inversion.
       destruct (build_app_comp (abseq r s a2_1 a2_2) p a) eqn:hi;
         try solve_by_inversion.
       specialize IHa1 with (a_st:=a_st) (a_st':=a) (o:=o0) (p:=p).
       concludes.
       destruct_conjs.
       specialize IHa2 with (a_st := a) (a_st':=a0) (o:=o1) (p:=p).
       concludes.
       subst.
       ff; eauto.
    +
                  destruct (build_app_comp a1 p a_st) eqn:hey;
         try solve_by_inversion.
       destruct (build_app_comp (abpar r s a2_1 a2_2) p a) eqn:hi;
         try solve_by_inversion.
       specialize IHa1 with (a_st:=a_st) (a_st':=a) (o:=o0) (p:=p).
       concludes.
       destruct_conjs.
       specialize IHa2 with (a_st := a) (a_st':=a0) (o:=o1) (p:=p).
       concludes.
       subst.
       ff; eauto. 
  -
    df.
    tauto.
  -
    df.
    tauto. 

 *)
      
Defined.

Ltac do_ba_st_const :=
  let tac := (eapply ba_const; eauto) in
  repeat (
      match goal with
      | [H: build_app_comp _ _ ?a_st = (_, ?a0) |- _] =>
        assert_new_proof_by (a_st = a0) tac
      end);
  subst.

Lemma allMappedSub' : forall a a_st e p,
    allMapped a a_st p e ->
    allMapped a a_st p mt.
Proof.
  induction a; intros.
  -
    destruct a.
    +
      allMappedFacts.
      econstructor.
      econstructor.
    +
      allMappedFacts.
      econstructor.
      econstructor.
      reflexivity.
      eexists.
      eauto.
    +
      allMappedFacts.
      econstructor.
      econstructor.
      reflexivity.
      eexists.
      eauto.
  -
    allMappedFacts.
    df.
    econstructor.
    reflexivity.
    reflexivity.
    eauto.
  -
    allMappedFacts.
    assert (allMapped a1 a_st p mt) by eauto.
    econstructor.
    eassumption.
    eassumption.
Defined.


Lemma allMappedSub : forall a a_st t p n,
    allMapped a a_st p (eval t n mt) ->
    allMapped a a_st p mt.
Proof.
  intros.
  eapply allMappedSub'; eauto.
Defined.

Lemma build_app_some : forall a a_st p,
    allMapped a a_st p mt ->
    exists o, build_app_comp a p a_st = (Some o, a_st).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    destruct a;
      try (cbn; df; eauto; tauto).
    +
      cbn.
      df.
      allMappedFacts.
      debound.
      subst'.
      df.
      eauto.
    +
      cbn.
      df.
      allMappedFacts.
      debound.
      subst'.
      df.
      eauto.
  -
    cbn.
    df.
    allMappedFacts.
    edestruct IHa.
    eassumption.
    destruct_conjs.
    simpl in *.
    df.
    subst'.
    df.
    eauto.
  -
    allMappedFacts.
    specialize IHa1 with (a_st:=a_st) (p:=p).
    specialize IHa2 with (a_st:=a_st) (p:=p).
    assert (allMapped a2 a_st p mt).
    eapply allMappedSub'; eauto.
    repeat concludes.
    destruct_conjs.
    df.

    destruct a2;
      try (subst'';
           df;
           eauto). 
    +
      destruct a;
        try (subst'; df; eauto).
      ++
        df.
        allMappedFacts.
        debound.
        subst'.
        df.
        do_ba_st_const.
        subst.
        subst'.
        df.
        eauto.
Defined.

Lemma ev_shape_transitive : forall e e' et et',
    Ev_Shape e et ->
    Ev_Shape e' et ->
    Ev_Shape e et' ->
    Ev_Shape e' et'.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; destruct et; intros;
    try repeat evShapeFacts; eauto; tauto.
Defined.

Lemma evShape_sub : forall a e1 e2 n1 et a_st v0 x vm_st vm_st',
    Ev_Shape e2 (eval (unanno a) n1 et) ->
    build_app_comp a n1 a_st = (Some v0, a_st) ->
    v0 vm_st = (Some x, vm_st') ->
    e2 = st_ev vm_st ->
    e1 = st_ev vm_st' ->
    Ev_Shape e1 et.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    destruct a.
    +
      ff; eauto.
    +
      df.
      dosome.
      ff.
      vmsts.
      df.
      evShapeFacts.
      df.
      eassumption.
    +
      df.
      dosome.
      ff.
      vmsts.
      df.
      evShapeFacts.
      df.
      eassumption.
  -
    df.
    eauto.
  -
    df.
    destruct a2 eqn:asp_eq.
    +
      destruct a eqn:a2_eq.
      ++
        doit.

        destruct v0.
        destruct vm_st.
        destruct vm_st'.
        
        
        simpl.
        simpl in H.  
        (*simpl in *. *)
        
        do_ba_st_const.
        eapply IHa1;
          [ eapply IHa2;
            try (simpl; eassumption);
            try tauto | eassumption | eassumption | tauto | tauto].

      ++
        doit.
        amsts.

        simpl.
        simpl in H.
        do_ba_st_const.

        eapply IHa1;
          [ eapply IHa2;
            try (simpl; eassumption);
            try tauto | eassumption | eassumption | tauto | tauto].

      ++

        doit.

        domap.
        do_pair.
            
        assert (exists o, build_app_comp (aasp r0 SIG) n1 a0 = (Some o, a0)).
        { eapply build_app_some.
          econstructor.
          econstructor.
          reflexivity.
          eexists.
          econstructor.
          eauto.
        }
        destruct_conjs.
        
        do_ba_st_const.

        doit.
            
        subst.
        cbn in H.

        assert (exists x y, H1 vm_st = (Some x, y)).
        {
          cbn in H2.
          df.
          dosome.
          eauto.
        }
        destruct_conjs.
        
        eapply IHa1.
        eapply IHa2.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        reflexivity.
        eassumption.
        eassumption.
        simpl.
        destruct vm_st.
        simpl in Heqp5.
        destruct H5.
        simpl.
        cbn in H2.
        repeat break_let.
        unfold bind in H2.
        simpl in H2.
        cbn in H2.
        repeat break_let.
              
        invc Heqp0.
        subst''.
        
        unfold ret in *.
        Print do_pair.
        do_pair.
        do_pair.
        doit.
        reflexivity.
        reflexivity.

    +
      doit.

      amsts.
      simpl.
      simpl in H.
      do_ba_st_const.
      eapply IHa1.
      eapply IHa2.
      simpl.
      eassumption.
      eassumption.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.

    +

      doit.

      amsts.
      simpl.
      simpl in H.
      do_ba_st_const.
      eapply IHa1.
      eapply IHa2.
      simpl.
      eassumption.
      eassumption.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.

      Unshelve.
      eauto.
Defined.

Lemma contratra : forall x (f:EvidenceC -> EvidenceC) (vmst vmst':vm_st),
    x = (None, vmst) ->
    x = (Some f, vmst') ->
    False.
Proof.
  intros.
  rewrite H in *.
  solve_by_inversion.
Defined.

Lemma build_app_run_some : forall a p a_st x v_st et e,
    e = st_ev v_st ->
    Ev_Shape e (eval (unanno a) p et) ->
    (*allMapped a a_st p et -> *)
    build_app_comp a p a_st = (Some x, a_st) ->
    exists y v, (x v_st = (Some y, v)).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    destruct a;
      try evShapeFacts.
    +
      df.
      eauto.    
    +
      df.
      doit.
      (*
      dosome.
      df. *)
      ff.

      ++
        eauto.
      ++
        vmsts.
        df.
        evShapeFacts.
        solve_by_inversion.
    +
      df.
      doit.

      ff.
      ++
        eauto.
      ++
        vmsts.
        df.
        evShapeFacts.
        solve_by_inversion.
  -
    df.
    eauto.
  -
    vmsts.
    df.
    subst.
    df.

    destruct a2 eqn:a2_eq.
    +
      destruct a eqn:a_eq.
      ++
        (*doit. *)    
        dosome_eqj.
        dosome_eqj.
        repeat break_let.

        do_pair.

        dosome_eqj.
        do_pair.
        
        
        do_ba_st_const.

        edestruct IHa2 with
            (v_st:=
               {|
                st_ev := st_ev;
                st_trace := st_trace;
                st_pl := st_pl;
                st_store := st_store |}) . 
        reflexivity.
        eassumption.
        eassumption.
        destruct_conjs.
        subst''.
        repeat break_let.
        
        amsts.

        edestruct IHa1 (*with
            (v_st:=
                {|
                st_ev := st_ev2;
                st_trace := st_trace2;
                st_pl := st_pl2;
                st_store := st_store2 |})*).
        reflexivity.
        eapply evShape_sub.
        eassumption.
        eassumption.
        eassumption.
        tauto.
        tauto.
        eassumption.
        destruct_conjs.
        subst''.
        repeat do_pair.
        eauto.

      ++

        dosome_eq hi.
        dosome_eq hey.
        repeat break_let.

        do_pair.

        dosome_eq hey.
        do_pair.
        do_ba_st_const.

        edestruct IHa2 with
            (v_st:=
               {|
                st_ev := st_ev;
                st_trace := st_trace;
                st_pl := st_pl;
                st_store := st_store |}) . 
        reflexivity.
        eassumption.
        eassumption.
        destruct_conjs.
        subst''.
        repeat break_let.
        Print vmsts.


        amsts.

        edestruct IHa1 (*with
            (v_st:=
                {|
                st_ev := st_ev2;
                st_trace := st_trace2;
                st_pl := st_pl2;
                st_store := st_store2 |})*).
        reflexivity.
        eapply evShape_sub.
        eassumption.
        eassumption.
        eassumption.
        tauto.
        tauto.
        eassumption.
        destruct_conjs.
        subst''.
        do_pair.
        inversion Heqp0.
        eauto.
      ++
        do_ba_st_const.
        df.
        dosome_eq hi.
        df.
        dosome_eq hey.
        df.
        
        simpl in H0.
        evShapeFacts.
        df.
        do_ba_st_const.
        vmsts.
        edestruct IHa1 with
            (v_st:=
               {|
            st_ev := e;
            st_trace := st_trace ++ [umeas n st_pl n3 [encodeEv e; bs]];
            st_pl := st_pl;
            st_store := st_store |}).
        reflexivity.
        eassumption.
        eassumption.
        destruct_conjs.
        vmsts.
        destruct o3.
        +++
          inversion Heqp5.
          eauto.
        +++
          df.

          exfalso.
          eapply contratra; eauto.

    +

      dosome_eq hi.
        dosome_eq hey.
        repeat break_let.

        do_pair.

        dosome_eq hey.
        do_pair.
        do_ba_st_const.

        edestruct IHa2 with
            (v_st:=
               {|
                st_ev := st_ev;
                st_trace := st_trace;
                st_pl := st_pl;
                st_store := st_store |}) . 
        reflexivity.
        eassumption.
        eassumption.
        destruct_conjs.
        subst''.
        repeat break_let.
        Print vmsts.


        amsts.

        edestruct IHa1 (*with
            (v_st:=
                {|
                st_ev := st_ev2;
                st_trace := st_trace2;
                st_pl := st_pl2;
                st_store := st_store2 |})*).
        reflexivity.
        eapply evShape_sub.
        eassumption.
        eassumption.
        eassumption.
        tauto.
        tauto.
        eassumption.
        destruct_conjs.
        subst''.
        do_pair.
        inversion Heqp0.
        eauto.
    +
      dosome_eq hi.
        dosome_eq hey.
        repeat break_let.

        do_pair.

        dosome_eq hey.
        do_pair.
        do_ba_st_const.

        edestruct IHa2 with
            (v_st:=
               {|
                st_ev := st_ev;
                st_trace := st_trace;
                st_pl := st_pl;
                st_store := st_store |}) . 
        reflexivity.
        eassumption.
        eassumption.
        destruct_conjs.
        subst''.
        repeat break_let.
        Print vmsts.


        amsts.

        edestruct IHa1 (*with
            (v_st:=
                {|
                st_ev := st_ev2;
                st_trace := st_trace2;
                st_pl := st_pl2;
                st_store := st_store2 |})*).
        reflexivity.
        eapply evShape_sub.
        eassumption.
        eassumption.
        eassumption.
        tauto.
        tauto.
        eassumption.
        destruct_conjs.
        subst''.
        do_pair.
        inversion Heqp0.
        eauto.
Defined.

Lemma same_ev_shape: forall t vmst vmst' e e_res et e_res_t p a_st x new_vmst new_vmst' f e'' app_ev,
  well_formed t ->
  build_comp t vmst = (Some tt, vmst') ->
  e = st_ev vmst ->
  Ev_Shape e et ->
  e_res = st_ev vmst' ->
  Ev_Shape e_res e_res_t ->
  build_app_comp t p a_st = (Some x, a_st) -> (* x : VM (EvidenceC -> EvidenceC) *)
  runSt new_vmst x = (Some f, new_vmst') ->
  Ev_Shape e'' et ->
  app_ev = f e'' ->
  Ev_Shape app_ev e_res_t.
Proof.
  intros.
  subst.
  vmsts.
  simpl in *.
  df.
  generalizeEverythingElse t.
  induction t; intros;
    try do_wf_pieces.
  -
    destruct r.
    destruct a.
    +
      df.
      dosome.
      eapply ev_shape_transitive.
      apply H2.
      eassumption.
      eassumption.
    +
      df.
      dosome.
      evShapeFacts.
      haaa.
      econstructor.
      eapply ev_shape_transitive.
      apply H2.
      eassumption.
      eassumption.
    +
      df.
      dosome.
      evShapeFacts.
      haaa.
      econstructor.
      eapply ev_shape_transitive.
      apply H2.
      eassumption.
      eassumption.
  (* HSH case
    +
      df.
      dosome.
      evShapeFacts.
     (* haaa. *)
      econstructor.
      eapply ev_shape_transitive.
      apply H1.
      eassumption.
      eassumption. *)
  -
    df.
    dohtac.
    df.
    eapply IHt.
    eassumption.
    apply build_comp_at.
    apply H2.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
  -
    df.
    dosome.
    destruct t2 eqn:t2_eq.
    ++
      vmsts.
      destruct a eqn:a_eq.
      +++
        break_match.
        dosome.
        do_ba_st_const.
        df.
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.

      +++
        break_match.
        dosome.
        do_ba_st_const.
        break_match; try solve_by_inversion.
        df.
        evShapeFacts.
        econstructor.
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
      +++
        break_match.
        dosome.
        do_ba_st_const.
        break_match; try solve_by_inversion.
        df.
        evShapeFacts.
        econstructor.
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
    ++

      dosome_eq hi.
      dosome_eq hey.
      repeat break_let.

      do_pair.

      dosome_eq hey.
      do_pair.
      do_ba_st_const.
      break_match; try solve_by_inversion.
      dosome_eq heey.
      repeat break_let.
      subst.
      do_pair.
      dosome_eq hii.
      do_pair.
      amsts.
      do_pl_immut.

      eapply IHt2.
      eassumption.
      eassumption.
      eapply multi_ev_eval.
      apply H1.
      eassumption.
      eassumption.
      reflexivity.
      eassumption.
      eassumption.
      eassumption.

      eapply IHt1.
      eassumption.
      eassumption.
      eassumption.
      eapply multi_ev_eval.
      apply H1.
      eassumption.
      eassumption.
      reflexivity.
      eassumption.
      eassumption.
      eassumption.
    ++
      dosome_eq hi.
      dosome_eq hey.
      repeat break_let.

      do_pair.

      dosome_eq hey.
      do_pair.
      do_ba_st_const.
      break_match; try solve_by_inversion.
      dosome_eq heey.
      repeat break_let.
      subst.
      do_pair.
      dosome_eq hii.
      do_pair.
      amsts.
      do_pl_immut.

      eapply IHt2.
      eassumption.
      eassumption.
      eapply multi_ev_eval.
      apply H1.
      eassumption.
      eassumption.
      reflexivity.
      eassumption.
      eassumption.
      eassumption.

      eapply IHt1.
      eassumption.
      eassumption.
      eassumption.
      eapply multi_ev_eval.
      apply H1.
      eassumption.
      eassumption.
      reflexivity.
      eassumption.
      eassumption.
      eassumption.
      Unshelve.
      eauto.
      eauto.
      exact (aasp (0,0) (ASPC 1 [])).
      exact mtc.
      eauto.
      eauto.
      exact (aasp (0,0) (ASPC 1 [])).
      exact mtc.
      eauto.
      eauto.
Defined.

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args, evidenceEvent (umeas n p i args)
(*| sev: forall n p, evidenceEvent (sign n p)
| hev: forall n p, evidenceEvent (hash n p)*) .


Definition measEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  events t p ev /\ evidenceEvent ev.

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p q i i' n n' m args st,
    m = st_aspmap st ->
    bound_to m (p,i) i' ->
    appEvent (umeas n p i args) st (umeas n' q i' ([n] ++ args)).

Ltac measEventFacts :=
  match goal with
  | [H: measEvent _ _ _ |- _] => invc H
  end.

Ltac evEventFacts :=
  match goal with
  | [H: evidenceEvent _ |- _] => invc H
  end.

Ltac invEvents :=
  match goal with
  | [H: events _ _ _  |- _] => invc H
  end.
    
Ltac dosome_eq' y :=
  match goal with
  | H:match ?x with
      | _ => _
      end _ = (Some _, _) |- _ => destruct x eqn:y; try solve_by_inversion
  end.

Lemma isnil{A:Type} : forall (ls xs : list A),
    ls = ls ++ xs ->
    xs = [].
Proof.
  intros.
  assert (ls = ls ++ []).
  {
    rewrite app_nil_r.
    tauto.
  }
  rewrite H0 in H at 1.
  eapply app_inv_head; eauto.
Defined.

Ltac dothat :=
  unfold StVM.st_ev, StVM.st_pl, StVM.st_trace, StVM.st_store in *;
  try unfold st_ev in *;
  try unfold st_pl in *;
  try unfold st_trace in *;
  try unfold st_store in *.

Ltac ff' :=
  repeat break_match; try solve_by_inversion.

Ltac doex := 
  unfold extractUev, extractSig in *;
  ff';
  unfold ret in *; doit.

Ltac do_inv_head :=
  let tac := (eapply app_inv_head; eauto) in
  repeat
    match goal with
    | [H: ?ls ++ ?xs = ?ls ++ ?ys |- _] => assert_new_proof_by (xs = ys) tac
    end.

Lemma trace_cumul : forall  t e a_st a_st' v tr tr' p n n' o o' e' o0,
    build_app_comp t p a_st = (Some v, a_st') ->
    v    {| st_ev := e;  st_trace := tr;  st_pl := n;  st_store := o |} =
    (Some o0, {| st_ev := e'; st_trace := tr'; st_pl := n'; st_store := o'|}) ->
    exists tr'', tr' = tr ++ tr''.
Proof.
  induction t; intros.
  -
    destruct a.
    +
      df.
      exists [].
      rewrite app_nil_r.
      eauto.
    +
      
      df.
      doit.
      unfold extractUev in *.
   
      dosome_eq' hi.
      df.
      eexists.
      reflexivity.
    +
      df.
      doit.
      unfold extractSig in *.
      dosome_eq' hi.
      df.
      eexists.
      reflexivity.
  -
    df.
    do_ba_st_const.
    eauto.
  -
    df.
    do_ba_st_const.
    destruct t2.
    +
      destruct a.
      ++
        doit.
        amsts.
        edestruct IHt1.
        eassumption.
        eassumption.
        subst.
        edestruct IHt2.
        eassumption.
        eassumption.
        subst.
        rewrite <- app_assoc.
        eexists.
        eauto.
      ++
        doit.
        amsts.
        edestruct IHt1.
        eassumption.
        eassumption.
        subst.
        edestruct IHt2.
        eassumption.
        eassumption.
        subst.
        rewrite <- app_assoc.
        eexists.
        eauto.
      ++
        doit.
        doex.
        dothat.

        edestruct IHt1.
        eassumption.
        eassumption.
        subst.
        eexists.
        rewrite app_assoc.
        reflexivity.
    +
      doit.
      amsts.
      edestruct IHt1.
      eassumption.
      eassumption.
      subst.
      edestruct IHt2.
      eassumption.
      eassumption.
      subst.
      rewrite <- app_assoc.
      eexists.
      eauto.
    +
      doit.
      amsts.
      edestruct IHt1.
      eassumption.
      eassumption.
      subst.
      edestruct IHt2.
      eassumption.
      eassumption.
      subst.
      rewrite <- app_assoc.
      eexists.
      eauto.
Defined.

Ltac do_cumul2 :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),

     H': ?v2 {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}),
    H'2: build_app_comp _ _ _ = (Some ?v2, _) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H'2 | apply H'])
    end.


Ltac do_cumul4 :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),
             
     H'': ?v {| st_ev := _; st_trace := ?tr3; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr3'; st_pl := _; st_store := _ |}),
     H''': ?v2 {| st_ev := _; st_trace := ?tr31; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr31'; st_pl := _; st_store := _ |}),

     H': ?v2 {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}),
    H'2: build_app_comp _ _ _ = (Some ?v2, _) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H'2 | apply H']);
      assert (exists tr'' : list Ev, tr3' = tr3 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H'']) ;
      assert (exists tr'' : list Ev, tr31' = tr31 ++ tr'')by (eapply trace_cumul; [apply H'2 | apply H'''])
    end.

Ltac do_cumul2' :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),
     H': ?v {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
           (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H'])
    end.

Ltac do_cumul1 :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H])
    end.

Ltac do_cumul := first [do_cumul4 | do_cumul2 | do_cumul2' | do_cumul1]; destruct_conjs.

Lemma dood : forall t vm_st vm_st' e e'' e' p a_st x0 x1 new_vmst new_vmst',
    build_comp t vm_st = (Some tt, vm_st') ->
    e = st_ev vm_st ->
    e' = st_ev vm_st' ->
    build_app_comp t p a_st = (Some x0, a_st) ->
    x0 new_vmst = (Some x1, new_vmst') ->
    e' = st_ev new_vmst -> 
    e'' = st_ev new_vmst' ->
    e = e''.
Proof.
  induction t; intros.
  -
    destruct a.
    +
      subst.
      amsts.
      df.
      reflexivity.
    +
      subst.
      amsts.
      df.
      dosome.
      reflexivity.
    +
      subst.
      amsts.
      df.
      dosome.
      reflexivity.
  -
    subst.
    amsts.
    df.
    dohtac.
    df.
    eapply IHt.
    apply build_comp_at.
    reflexivity.
    reflexivity.
    eassumption.
    eassumption.
    tauto.
    tauto.
  -
    subst.
    amsts.
    df.    
    dosome. 
    destruct t2.
    +
      destruct a eqn:aeq.
      ++
        doit.
        cbn in Heqp2.
        doex.
        amsts.
        cbn in Heqp1.
        doit.
        eauto.
      ++
        clear IHt2.
        df.
        dosome.
        haaa.
      ++
        clear IHt2.
        df.
        dosome.
        haaa.
    +
      doit.

      amsts.
      do_ba_st_const.
      do_pl_immut.

      assert (st_ev3 = st_ev1).
      eapply IHt2.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
      subst.

      eapply IHt1.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
    +
      doit.

      amsts.
      do_ba_st_const.
      do_pl_immut.

      assert (st_ev3 = st_ev1).
      eapply IHt2.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
      subst.

      eapply IHt1.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
      Unshelve.
      eauto.
      eauto.
      exact (aasp (0,0) (ASPC 1 [])).
      exact mtc.
      eauto.
      eauto.
      exact (aasp (0,0) (ASPC 1 [])).
      exact mtc.
      eauto.
      eauto.
Defined.

Lemma appraisal_correct : forall t vmst vmst' p e_res new_vmst new_vmst' a_st x f tr_app ev,
    build_comp t vmst = (Some tt, vmst') ->
    p = st_pl vmst ->
    e_res = st_ev vmst' ->
    e_res = st_ev new_vmst ->
    build_app_comp t p a_st = (Some x, a_st) -> (* x : VM (EvidenceC -> EvidenceC) *)
    runSt new_vmst x = (Some f, new_vmst') ->
    tr_app = st_trace new_vmst' ->
    measEvent t p ev ->
    exists ev', In ev' tr_app /\ appEvent ev a_st ev'.
Proof.
  induction t; intros.
  -
    destruct a.
    +
      measEventFacts.
      evEventFacts.
      solve_by_inversion.
    +
      measEventFacts.
      evEventFacts.
      invEvents.
      destruct r.
      simpl.
          
      amsts.
      dothat.
      subst.
      df.
      doit.
      doex.
      df.

      exists (umeas b st_pl n1 (b :: args)).
      split.
      ++
        Print In.
        Search In.
        eapply in_or_app.
        right.
        econstructor. reflexivity.
      ++
        assert (b::args = [b] ++ args).
        reflexivity.
        rewrite H.
        econstructor.
        reflexivity.
        econstructor.
        eassumption.
    +
      measEventFacts.
      evEventFacts.
      solve_by_inversion.
  -
    amsts.
    subst.
    df.
    dohtac.
    df.

    measEventFacts.
    evEventFacts.
    invEvents.

    edestruct IHt with
        (vmst:=
           {| st_ev := st_ev3; st_trace := []; st_pl := n; st_store := [] |})
        (new_vmst:=
           {| st_ev := toRemote (unanno t) st_ev3;
              st_trace := st_trace0;
              st_pl := st_pl0;
              st_store := st_store0 |}).
    
    apply build_comp_at.
    reflexivity.
    reflexivity.
    tauto.
    eassumption.
    eassumption.
    reflexivity.
    simpl.
    econstructor.
    eassumption.
    econstructor.
     
    destruct_conjs.
    eexists.
    split; eauto.

  - (* alseq case *)
    df.
    dosome_eq hi.
    do_pair.
    amsts.
    df.
    subst.
    destruct t2.
    +
      destruct a eqn:aeq.
      ++
        doit.
        amsts.
        doex.
        
        simpl in Heqp.
        doex. 
        measEventFacts.
        evEventFacts.
        invEvents.
        +++
          do_pl_immut.
          cbn in Heqp1.
          do_pair.

          eapply IHt1 with
              (vmst:= {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst := {| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          eassumption.
          econstructor.
        +++
          solve_by_inversion.
      ++

        doit.
        amsts.
        measEventFacts.
        evEventFacts.
        invEvents.
        +++
          do_pl_immut.
          do_ba_st_const.
          df.
          dosome.
          haaa.
          
          eapply IHt1 with
              (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst:= {|
                  st_ev := st_ev2;
                  st_trace := st_trace1 ++ [umeas n3 st_pl4 n5 (n3 :: l)];
                  st_pl := st_pl4;
                  st_store := st_store4 |}).
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          eassumption.
          econstructor.
        +++
          do_pl_immut.
          do_ba_st_const.
          invEvents.
          
          edestruct IHt2 with
              (vmst:={| st_ev := st_ev; st_trace := st_trace; st_pl := p; st_store := st_store |})
              (new_vmst:={| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          econstructor.
          reflexivity.
          econstructor.
          simpl in H.
          destruct_conjs.
          destruct r.
          simpl in H1.
          simpl.
          exists x.
          Print do_cumul2.
          do_cumul.
          subst.
          split.
          apply in_or_app.
          eauto.
          eauto.
      ++
        doit.
        doex.
        dothat.
        
        amsts.
        do_ba_st_const.
        do_pl_immut.
        measEventFacts.
        evEventFacts.
        invEvents.
        +++
          clear IHt2.
          df.
          
          eapply IHt1 with
              (vmst:=
                 {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst:= {|
                  st_ev := e;
                  st_trace := st_trace4 ++ [umeas n st_pl4 n1 [encodeEv e; b]];
                  st_pl := st_pl4;
                  st_store := st_store4 |}).
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          eassumption.
          econstructor.
        +++
          invEvents.

    +
      doit.
      amsts.
      measEventFacts.
      evEventFacts.
      invEvents.
      ++
        clear IHt2.
        df.
        dohtac.
        df.
        do_pl_immut.
        do_ba_st_const.
        eapply IHt1 with (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |}) (new_vmst:={| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
        eassumption.
        tauto.
        tauto.

        simpl.
        assert (st_ev4 = st_ev2).
        { 
          Check dood.
          eapply dood with (vm_st0 := {| st_ev := st_ev4; st_trace := []; st_pl := n1; st_store := [] |}).
          apply build_comp_at.
          tauto.
          tauto.
          apply Heqp.
          eassumption.
          tauto.
          tauto.
        }
        subst.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        eassumption.
        econstructor.
      ++
        do_pl_immut.
        do_ba_st_const.
        cbn in Heqp1.
        repeat break_let.
        df.
        dohtac.
        dosome.
        do_pl_immut.
        do_ba_st_const.
        amsts.
        df.
        invEvents.
        edestruct IHt2 with (vmst:={| st_ev := st_ev; st_trace := []; st_pl := n1; st_store := [] |}) (new_vmst:={| st_ev := toRemote (unanno t2) st_ev; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
        tauto.
        tauto.

        tauto.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        apply evtsatt.
        eassumption.
        econstructor.
   
        destruct_conjs.
        simpl in H1.
        do_cumul.
        subst.

        exists x.
        split.
        +++
          eapply in_or_app.
          eauto.
        +++
          eauto.
    +
      doit.
      amsts.
      measEventFacts.
      evEventFacts.
      invEvents.
      ++
        clear IHt2.
        do_pl_immut.
        do_ba_st_const.
        eapply IHt1 with
            (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
            (new_vmst:={| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
        eassumption.
        tauto.
        tauto.

        simpl.
        assert (st_ev = st_ev2).
        {
          Check dood.
          eapply dood.
          apply Heqp1.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          tauto.
        }
        subst.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        eassumption.
        econstructor.
      ++
        do_pl_immut.
        do_ba_st_const.
        
        edestruct IHt2 with
            (vmst:={| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl2; st_store := st_store |})
            (new_vmst:={| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
        eassumption.
        tauto.
        tauto.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        eassumption.
        econstructor.
        destruct_conjs.

        do_cumul.
        subst.
        eexists.
        split.
        +++
          apply in_or_app.
          eauto.
        +++
          eauto.
          
          Unshelve.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
Defined.










(*
(***** Potentially-failing appraisal functions ******) 


Definition fromOpt{A:Type} (o:option A) (a:A) : A :=
  match o with
  | Some t => t
  | None => a
  end.

Definition run_app_comp (t:AnnoTerm) (p:Plc) (a_st:AM_St) (e_in:EvidenceC) : (EvidenceC -> EvidenceC) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt a_st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in (* (option (EvidenceC -> EvidenceC) * VM_St) *)
  fromOpt (fst vres_opt) ((fun _ => mtc)).

Definition run_app_comp' (t:AnnoTerm) (p:Plc) (st:AM_St) (e_in:EvidenceC) : ((option (EvidenceC -> EvidenceC)) * vm_st) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in
  vres_opt.


Definition at1 := (asp (ASPC 11 [])).
(*Definition at2 := (asp (ASPC 22 [])). *)
Definition term := lseq at1 (asp SIG).
Definition aterm := annotated term.
Compute aterm.

Check run_vm.

Definition aterm_vm_st := run_vm aterm empty_vmst.
Compute aterm_vm_st.
Definition aterm_ev := st_ev aterm_vm_st.
Compute aterm_ev.

Definition ast :=
  mkAM_St [] 0 [((0,11),34); ((0,22),45)] [(0,42)].

Compute run_app_comp' aterm 0 ast aterm_ev.

Compute run_app_comp aterm 0 ast aterm_ev.
*)





(*
Definition run_app_comp (t:AnnoTerm) (p:Plc) (a_st:AM_St) (e_in:EvidenceC) : (EvidenceC -> EvidenceC) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt a_st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in (* (option (EvidenceC -> EvidenceC) * VM_St) *)
  fromOpt (fst vres_opt) ((fun _ => mtc)).

Definition run_app_comp' (t:AnnoTerm) (p:Plc) (st:AM_St) (e_in:EvidenceC) : ((option (EvidenceC -> EvidenceC)) * vm_st) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in
  vres_opt.
 *)

(*
Lemma measEventAt' : forall t n p q ev,
    measEvent (snd (anno (att n t) q)) p ev ->
    measEvent (snd (anno t (S q))) n ev.
Proof.

  induction t; intros;
    try (
      df;
      measEventFacts;
      evEventFacts;
      invEvents;
      invEvents;
      try (repeat econstructor; eauto; tauto)).
Defined.
*)





(*
(***** Old Proofs, potentially-failing appraisal *****)

Lemma gogo' : forall t p a a' o_res o_res' v1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0 x1,
    build_app_comp t p a = (Some v1, a') ->
    v1 {| st_ev := e2; st_trace := tr1; st_pl := p1; st_store := o1 |} =
    (Some o_res, {| st_ev := e1'; st_trace := tr1 ++ x1; st_pl := p1'; st_store := o1' |}) ->
    v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
    (Some o_res', {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) ->
    x0 = x1.
Proof.
  induction t; intros.
  -
    destruct r; destruct a.
    +
      df. 
      assert (x1 = []) by (eapply isnil; eauto).
      assert (x0 = []) by (eapply isnil; eauto).
      congruence.
    +
      df.
      doit.
      domap.
      doit.
      dothat.
      doex.
      do_inv_head.
      congruence.
    +
      df.
      doit.
      domap.
      doit.
      dothat.
      doex.
      do_inv_head.
      congruence.
  -
    df.
    eauto.
  -
    df.
    destruct r.
    subst.
    destruct t2.
    +
      doit.
      destruct a0.
      ++
        doit.

        cbn in Heqp0.
        repeat break_let.
        doex.
        eauto.
      ++
        doit.
        cbn in Heqp0.
        df.
        doit.
        domap.
        doit.
        doex.
        
        repeat break_let.
        doex.
        doit.
        df.
        doit.
        subst.
        invc Heqe.
        eauto.
        do_cumul.
        assert (x0 = [umeas n4 0 n1 (b :: l)] ++ H0).
        {
          admit.
        }

        assert (x1 = [umeas n4 0 n1 (b :: l)] ++ H1).
        {
          admit.
        }
        assert (H0 = H1).
        {
          admit.
        }
        subst.
        congruence.
      ++
        doit.
        doex.
        dothat.
        subst.
        invc Heqe4.

        do_cumul.
        assert (x0 = [umeas n 0 n3 [encodeEv e; b]] ++ H).
        {
          admit.
        }

        assert (x1 = [umeas n 0 n3 [encodeEv e; b]] ++ H0).
        {
          admit.
        }
        assert (H = H0).
        {
          admit.
        }
        subst.
        congruence.
    +
      doit.
      cbn in Heqp0.
      amsts.
      do_cumul.
      subst.
      assert (x0 = H3 ++ H).
      {
        admit.
      }
      subst.
      assert (x1 = H0 ++ H4).
      {
        admit.
      }
      subst.
      assert (H = H4).
      eapply IHt1.
      eassumption.
      rewrite app_assoc in *.
      eassumption.
      repeat rewrite app_assoc in *.
      assert (st_ev = st_ev0).
      {
        admit.
      }
      subst.
      eassumption.
      subst.
      assert (H3 = H0) by eauto.
      subst.
      reflexivity.
   +
      doit.
      
      (*cbn in Heqp0. *)
      amsts.
      do_cumul.
      subst.
      assert (x0 = H3 ++ H).
      {
        admit.
      }
      subst.
      assert (x1 = H0 ++ H4).
      {
        admit.
      }
      subst.
      assert (H = H4).
      eapply IHt1.
      eassumption.
      rewrite app_assoc in *.
      eassumption.
      repeat rewrite app_assoc in *.
      assert (st_ev = st_ev0).
      {
        admit.
      }
      subst.
      eassumption.
      subst.
      assert (H3 = H0) by eauto.
      subst.
      reflexivity.
      Unshelve.
      eauto.
        
    
    
      
      
      

      
      
      

      
      











(*

  
  assert (Ev_Shape e et).
  eapply gen_ev_shape; eauto.
  generalizeEverythingElse e.

  induction e;
    intros;
    evShapeFacts;
    try
      ( df;
        dosome;
        haaa;
        do_cumul;
        repeat subst'';                                                           
        repeat dof;
        assert (H0 = H1) by ( eapply IHe; eauto);
        congruence);
    try
      ( df;
        dosome;
        repeat break_match; try solve_by_inversion;
        df;
        eauto).
  -
    df.
    assert (x0 = []).
    eapply lista; eauto.
    assert (x1 = []).
    eapply lista; eauto.
    congruence.
  -
    df.
    dosome.
    repeat break_match; try solve_by_inversion.
    vmsts.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp1.
    subst.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp3.
    subst.

    assert (x = x2).
    eauto.
    subst.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp4.
    rewrite H in *.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp2.
    rewrite H0 in *.

    assert (x = x3).
    eauto.
    subst.

    assert (x0 = x2 ++ x3).
    {
      assert ((tr2 ++ x2) ++ x3 = tr2 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H1 in H.
      eapply app_inv_head.
      eassumption.
    }

    assert (x1 = x2 ++ x3).
    {
      assert ((tr1 ++ x2) ++ x3 = tr1 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H2 in H0.
      eapply app_inv_head.
      eassumption.
    }
    congruence.
    
  -
    df.
    dosome.
    repeat break_match; try solve_by_inversion.
    vmsts.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp1.
    subst.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp3.
    subst.

    assert (x = x2).
    eauto.
    subst.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp4.
    rewrite H in *.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp2.
    rewrite H0 in *.

    assert (x = x3).
    eauto.
    subst.

    assert (x0 = x2 ++ x3).
    {
      assert ((tr2 ++ x2) ++ x3 = tr2 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H1 in H.
      eapply app_inv_head.
      eassumption.
    }

    assert (x1 = x2 ++ x3).
    {
      assert ((tr1 ++ x2) ++ x3 = tr1 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H2 in H0.
      eapply app_inv_head.
      eassumption.
    }
    congruence.
Defined.
   *)
Admitted.


Lemma gogo : forall t p a a' o_res o_res' v1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0,
    build_app_comp t p a = (Some v1, a') ->
    v1 {| st_ev := e2; st_trace := []; st_pl := p1; st_store := o1 |} =
    (Some o_res, {| st_ev := e1'; st_trace := tr1; st_pl := p1'; st_store := o1' |}) ->
    v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
    (Some o_res', {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) ->
    x0 = tr1.
Proof.
  intros.
  eapply gogo'.
  eassumption.
  assert (tr1 = [] ++ tr1).
  simpl.
  reflexivity.
  subst''.
  eassumption.
  eassumption.
Defined.

Ltac do_gogo :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := []; st_pl := _; st_store := _ |} =
         (Some _, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),
     H': ?v {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
           (Some _, {| st_ev := _; st_trace := ?tr2 ++ ?tr2'; st_pl := _; st_store := _ |}) |- _] =>

      assert (tr2' = tr1')by (eapply gogo; [apply H2 | apply H | apply H'])
    end.
*)

(*
Lemma foofoo : forall t f p tr_n p_n o_n a0 a' v e' tr' p' o' e'' tr'' p'' o'',
    build_app_comp t p a0 = (Some v, a') ->
    v {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (Some f, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) ->
    (exists g e3 tr3 p3 o3,
        v {| st_ev := e'; st_trace := tr_n; st_pl := p_n; st_store := o_n |} =
        (Some g, {| st_ev := e3; st_trace := tr3; st_pl := p3; st_store := o3 |})).
Proof.
Admitted.

*)
