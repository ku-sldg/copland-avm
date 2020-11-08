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

Definition test_phrase_match (t:Term) : nat :=
  match t with
  | lseq t (asp SIG) => 3
  | _ => 3
  end.

Definition invokeUSM' (x:nat) (i:ASP_ID) (l:list Arg) : VM EvidenceC :=
  e <- get_ev ;;
  p <- get_pl ;;
  add_tracem [Term.umeas x p i l];;
  ret (uuc i x e).

Definition checkSig (x:nat) (i:ASP_ID) (l:list Arg) : VM BS :=
  (*p <- get_pl ;; *)
  add_tracem [Term.umeas x 0 i l];;
  ret 78.

Print EvidenceC.

Definition extractUev (e:EvidenceC) : VM (BS * EvidenceC) :=
  match e with
  | uuc i bs e' => ret (bs,e')
  | _ => failm
  end.


Definition checkUSM (x:nat) (i:ASP_ID) (l:list Arg) (bs:BS) : VM BS :=
  (* p <- get_pl ;; *)
  add_tracem [Term.umeas x 0 i ([bs] ++ l)] ;;
  ret 56.

Compute (eval (lseq (asp (ASPC 42 [42;42])) (asp (ASPC 43 [43;43]))) 0 (uu 1 [2;3] 0 mt)).

Compute (eval (lseq (asp (ASPC 43 [43;43])) (asp (ASPC 42 [42;42]))) 0 (uu 1 [2;3] 0 mt)).

(*
Compute (eval (bseq (ALL,NONE) (asp (ASPC 1 [1;1])) (asp (ASPC 2 [2;2]))) 0 (uu 1 [2;3] 0 mt)).
*)


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
        res <- checkSig n app_id ([encodeEv e'] ++ [bs] (* ++ args*) ) ;;
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
          (*
        e <- get_ev ;;
        pr <- extractComp e ;;
        let '(e1,e2) := pr in
        put_ev e1 ;;
        e1_res <- c ;;
        put_ev e2 ;;
        e2_res <- d ;;
        ret (ssc e1_res e2_res)*)) in
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
        res <- checkSig n app_id ([encodeEv e'] ++ [bs] (* ++ args*) ) ;;
        put_ev e' ;;
        ret (fun x => ggc res x) in
        
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
        
    ret c     *)
        

  | aasp (n,n') (CPY) =>
    
    (*p <- gets am_pl ;; *)
   (* app_id <- am_get_sig_asp p ;; *) (* TODO: get_hsh_asp impl *) 
    let c :=
        (*e <- get_ev ;; *)
        (*
        pr <- extractHsh e ;;
        let '(bs,e') := pr in
        (*
        res <- checkSig n app_id ([encodeEv e'] ++ [bs] (* ++ args*) ) ;;
        put_ev e' ;; (* TODO: does this have any effect? *) 
        ret (ggc res e') *)
        put_ev e' ;;
        ret (hhc 0 mtc) *)
        ret (fun x => x) in
        
    ret c
        
  | aatt r q t' =>
    (*modify_plc q ;; *)
    build_app_comp t' q
  (*| _ => ret (ret (fun _ => mtc)) *)
  end.

(*
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
    evMapped (hh p e') st *)

(*
            
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
    evMapped (pp e1 e2) st *).
Print eval.
Print eval_asp.


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
 (* | [H: evMapped (hh _ _) _ |- _] => invc H *)
                                        (*
  | [H: evMapped (nn _ _) _ |- _] => invc H
  | [H: evMapped (ss _ _) _ |- _] => invc H
  | [H: evMapped (pp _ _) _ |- _] => invc H  *)
  end;
  destruct_conjs;
  try debound.

Ltac allMappedFacts :=
  (*
  unfold allMapped in *;
  df;
  try evMappedFacts. *)

  
  match goal with
  | [H: allMapped (aasp _ _) _ _ _ |- _] => invc H
  | [H: allMapped (aatt _ _ _) _ _ _ |- _] => invc H
  | [H: allMapped (alseq _ _ _) _ _ _ |- _] => invc H
 (* | [H: allMapped (abseq _ _ _ _) _ _ _ |- _] => invc H
  | [H: allMapped (abpar _ _ _ _) _ _ _ |- _] => invc H *)
  end;
  destruct_conjs.



Lemma allMappedAt : forall r n a p st e (*x y z z'*),
    (*st = mkAM_St x y z z'-> *)
    allMapped (aatt r n a) st p e ->
    allMapped a (*(mkAM_St x y z z')*) st n e.
Proof.
  intros.
  allMappedFacts.
  df.
  eauto.
Defined.

(*

  unfold allMapped in *.
  df.
  eassumption.
Defined. *)

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
  (*| [H: Ev_Shape (hhc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (hh _ _) |- _] => invc H *)
                                        (*
  | [H: Ev_Shape (nnc _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (nn _ _) |- _] => invc H
  | [H: Ev_Shape (ssc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (ss _ _) |- _] => invc H
  | [H: Ev_Shape (ppc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (pp _ _) |- _] => invc H *)
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

Ltac subst'' :=
  match goal with
  | H:?A = _, H2:context [ ?A ] |- _ => rewrite H in *
  | H:?A = _ |- context [ ?A ] => rewrite H in *
  end.
Check build_app_comp.
Lemma ba_const : forall a a_st a_st' o p,
    build_app_comp a p a_st = (o, a_st') ->
    a_st = a_st'.
  (*
    am_nonceMap a_st = am_nonceMap a_st' /\
    am_nonceId a_st = am_nonceId a_st' /\
    st_aspmap a_st = st_aspmap a_st' /\
    st_sigmap a_st = st_sigmap a_st'. *)
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
      (*
             destruct gen_const with (e:=ee) (et:=?et) (a:=?A) (a':=?B) (o:=?o);
             try eassumption *)
      end);
  subst.

(*
Lemma mt_not_mt : forall e t p,
    e <> mt ->
    eval t p e <> mt.
Proof.
Admitted.

Lemma evMappedExtra : forall a p e a_st,
    evMapped (eval (unanno a) p e) a_st ->
    evMapped (eval (unanno a) p mt) a_st.
Proof.
Admitted.
*)

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

        (*
      ++
        subst'.
        df.
        (*
        cbn in *.
        unfold bind in H0.
        cbn in H0.
        break_let.
        break_let.
        break_let.
        break_let.
        invc H0. *)
        allMappedFacts.
        debound.
        haaa. *)
      ++
        df.
        allMappedFacts.
        debound.
        subst'.
        df.
        do_ba_st_const.
        (*
        assert (a4 = a).
        {
          eapply ba_const; eauto.
        } *)
        subst.
        subst'.
        df.
        eauto.
      
        
      

(*
  -
    df.
    eauto.
  -
    df.
    eauto. *)
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

Ltac domap :=
  let n := fresh in
  match goal with
  | [H: match ?X with _ => _ end _ = (Some _, _) |- _] =>
    destruct X eqn:n; try solve_by_inversion
  end.

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
        (*
    +
      df.
      dosome.
      df.

      repeat break_match; try solve_by_inversion.
      ++
        df.
        eauto.
      ++
        df.
        vmsts.
        df.
        evShapeFacts.
        df. *)
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
        


        
(*
        doit. *)


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
            st_trace := st_trace ++ [umeas n 0 n3 [encodeEv e; bs]];
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
          Lemma contratra : forall x (f:EvidenceC -> EvidenceC) (vmst vmst':vm_st),
            x = (None, vmst) ->
            x = (Some f, vmst') ->
            False.
          Proof.
            intros.
            rewrite H in *.
            solve_by_inversion.
          Defined.

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


(*
Lemma fafafaf : forall e tr p o tr' (x:VM (EvidenceC -> EvidenceC)) a a_st p' p'' o'',
    build_app_comp a p' a_st = (Some x, a_st) -> 
    fst (x {| st_ev := e; st_trace := tr; st_pl := p; st_store := o |}) =
    fst (x {| st_ev := e; st_trace := tr'; st_pl := p''; st_store := o'' |}).
Proof.
Admitted.
*)
Print AnnoTerm.

(*
Lemma same_ev_shape : forall a a_st e e_res vm_st p et e' t q,
    allMapped a a_st p et ->
    (*p = am_pl a_st -> *)
    (*Ev_Shape e' (eval (unanno t) q mt) -> *)

    Ev_Shape e'' (eval (unano t) q mt) ->
    e'' = (run_app_comp t q a_st e') mtc

    vm_st = run_vm a {| st_ev := e'; st_trace := []; st_pl := 0; st_store := [] |} ->
    e_res = st_ev vm_st ->
    Ev_Shape e_res e_res_t ->
    (*e_res_t = eval (unanno a) 0 et ->*)
    (*Ev_Shape e'' et ->*)
    e = (run_app_comp a p a_st e_res) e''  (*TODO: remove func, just add extra lseq term for initial appraising initial evidence *) ->
    Ev_Shape e e_res_t.
 *)


(*
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
Admitted.
*)

(*
Lemma evShapeAt : forall e et a n,
    well_formed a -> 
    Ev_Shape e et ->
    Ev_Shape (toRemote (unanno a) e) (eval (unanno a) n et).
Proof.
  intros.
  eapply multi_ev_eval.
  eassumption.
  apply build_comp_at.
  eassumption.
  reflexivity.
  Unshelve.
  exact [].
Defined.
*)

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
     (* evShapeFacts. 
      haaa.
      econstructor. *)
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
        (*break_match; try solve_by_inversion. *)
        df.
        (*evShapeFacts.
        econstructor. *)
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
      
(* OLD EV_SHAPE LEMMA 
Lemma same_ev_shape : forall a a_st p et vm_st vm_st' e_res e_res_t e' e'' e,
    allMapped a a_st p et ->
    well_formed a ->
    vm_st' = run_vm a vm_st ->
    p = st_pl vm_st ->
    e_res = st_ev vm_st' ->
    Ev_Shape e_res e_res_t ->
    e' = st_ev vm_st ->
    Ev_Shape e' et ->
    Ev_Shape e'' et ->
    (*e_res_t = eval (unanno a) 0 et ->*)
    e = (run_app_comp a p a_st e_res) e''
    (*TODO: remove func, just add extra lseq term for initial appraising initial evidence *) ->
    Ev_Shape e e_res_t.
 *)

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

Ltac dosome_eq' y :=
  match goal with
  | H:match ?x with
      | _ => _
      end _ = (Some _, _) |- _ => destruct x eqn:y; try solve_by_inversion
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
      dosome.
      dosome_eq' hey.
      df.
      unfold extractUev in *.
      dosome_eq' hi.
      df.
      eexists.
      reflexivity.
    +
      df.
      dosome.
      dosome_eq' hey.
      df.
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

        
        simpl in Heqp6.
        dosome_eq' hihihihi.
        do_pair.
        (*
        simpl in heyyyy. *)
        unfold extractSig in *.
        dosome_eq' ho.
        unfold ret in *.
        do_pair.

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
  (*let tac x y := (eapply trace_cumul; [apply x | apply y]) in *)
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
         H2: build_app_comp _ _ _ = (Some ?v, _),
       H': ?v2 {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}),
           H'2: build_app_comp _ _ _ = (Some ?v2, _) |- _] =>

      (*
      assert_new_proof_by (exists tr'' : list Ev, tr1' = tr1 ++ tr'') (tac H2 H) ;
      assert_new_proof_by (exists tr'' : list Ev, tr2' = tr2 ++ tr'') (tac H'2 H') *)
      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H'2 | apply H'])
    end.

Ltac do_cumul2' :=
 (* let tac x y := (eapply trace_cumul; [apply x | apply y]) in *)
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
         H2: build_app_comp _ _ _ = (Some ?v, _),
       H': ?v {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
           (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}) |- _] =>
      (*
      assert_new_proof_by (exists tr'' : list Ev, tr1' = tr1 ++ tr'') (tac H2 H) ;
      assert_new_proof_by (exists tr'' : list Ev, tr2' = tr2 ++ tr'') (tac H2 H') *)
      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H'])
    end.

Ltac do_cumul1 :=
  (*let tac x y := (eapply trace_cumul; [apply x | apply y]) in *)
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
         H2: build_app_comp _ _ _ = (Some ?v, _) |- _] =>
      (*
      assert_new_proof_by (exists tr'' : list Ev, tr1' = tr1 ++ tr'') (tac H2 H)
       *)
      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H])
    end.

Ltac do_cumul := first [do_cumul2 | do_cumul2' | do_cumul1]; destruct_conjs.

Lemma gogo' : forall t p a a' o_res o_res' v1 e1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0 x1,
    build_app_comp t p a = (Some v1, a') ->
    v1 {| st_ev := e1; st_trace := tr1; st_pl := p1; st_store := o1 |} =
    (Some o_res, {| st_ev := e1'; st_trace := tr1 ++ x1; st_pl := p1'; st_store := o1' |}) ->
    v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
    (Some o_res', {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) ->
    x0 = x1.
Proof.
  (*
  intros.
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


Lemma gogo : forall t p a a' o_res o_res' v1 e1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0,
    build_app_comp t p a = (Some v1, a') ->
    v1 {| st_ev := e1; st_trace := []; st_pl := p1; st_store := o1 |} =
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


Lemma foofoo : forall t f p tr_n p_n o_n a0 a' v e' tr' p' o' e'' tr'' p'' o'',
    build_app_comp t p a0 = (Some v, a') ->
    v {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (Some f, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) ->
    (exists g e3 tr3 p3 o3,
        v {| st_ev := e'; st_trace := tr_n; st_pl := p_n; st_store := o_n |} =
        (Some g, {| st_ev := e3; st_trace := tr3; st_pl := p3; st_store := o3 |})).
Proof.
Admitted.

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
        dosome_eq hi.
        dosome_eq hey.
        repeat break_let.
        do_pair.
        dosome_eq hey.
        do_pair.
        dosome_eq hey.
        dosome_eq heyy.
        repeat break_let.
        do_pair.
        dosome_eq heey.
        do_pair.
        cbn in Heqp3.
        repeat break_let.
        unfold ret in *.
        do_pair.
        do_pair.
        amsts.
        cbn in Heqp1.
        do_pair.
        eauto.
      ++
        dosome_eq hi.
        dosome_eq hey.
        repeat break_let.
        do_pair.
        dosome_eq hey.
        do_pair.
        dosome_eq hey.
        dosome_eq heyy.
        repeat break_let.
        do_pair.
        dosome_eq heey.
        do_pair.
        amsts.
        cbn in Heqp1.
        clear IHt2. df.
        dosome.
        haaa.
      ++
        clear IHt2.
        df.
        dosome.

        haaa.
    +
      do_ba_st_const.
      dosome_eq hi.
      dosome_eq hey.
      repeat break_let.
      do_pair.
      dosome_eq hii.
      do_pair.
      dosome_eq heey.
      dosome_eq hii.
      repeat break_let.
      do_pair.
      dosome_eq hee.
      do_pair.

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
      do_ba_st_const.
      dosome_eq hi.
      dosome_eq hey.
      repeat break_let.
      do_pair.
      dosome_eq hii.
      do_pair.
      dosome_eq heey.
      dosome_eq hii.
      repeat break_let.
      do_pair.
      dosome_eq hee.
      do_pair.

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

    (*well_formed t -> *)
    build_comp t vmst = (Some tt, vmst') ->
    (*e = st_ev vmst ->
  Ev_Shape e et -> *)
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
      invc H6.
      invc H8.
      solve_by_inversion.
    +
      measEventFacts.
      invc H8.
      invc H7.
      destruct r.
      simpl.
      
      
      amsts.
      unfold StVM.st_ev in *.
      unfold StVM.st_pl in *.
      unfold StVM.st_trace in *.
      subst.
      df.
      dosome_eq hey.
      do_pair.
      repeat break_let.
      do_pair.
      dosome_eq hey.
      df.
      dosome_eq' heyy.
      df.
      exists (umeas b 0 n1 (b :: args)).
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
      invc H8.
      solve_by_inversion.
  -
    amsts.
    subst.
    df.
    dohtac.
    df.

    measEventFacts.
    evEventFacts.
    invc H.
     
    edestruct foofoo.
    eassumption.
    eassumption.
    destruct_conjs.

    edestruct IHt with (vmst:={| st_ev := st_ev3; st_trace := []; st_pl := n; st_store := [] |}) (new_vmst:={| st_ev := toRemote (unanno t) st_ev3; st_trace := []; st_pl := 0; st_store := [] |}).
    
    apply build_comp_at.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    tauto.
    simpl.
    eassumption.
    apply H5.
    simpl.
    reflexivity.
    simpl.
    econstructor.
    eassumption.
    econstructor.


    
    assert (st_trace = st_trace0 ++ H0).
    {
      Print do_cumul2'.
      do_cumul.
      
      subst.
      assert (H8 = H9).
      {
        eapply gogo; eauto.
      }
      subst.
      simpl.
      reflexivity.
    }
    subst.
    destruct_conjs.
    exists x1.
    split.
    +
      eapply in_or_app.
      eauto.
    +
      eauto.
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
        dosome_eq hi.
        dosome_eq hey.
        subst.
        repeat break_let.
        do_pair.
        dosome_eq hii.
        subst.
        do_pair.
        dosome_eq hii.
        dosome_eq hey.
        subst.
        repeat break_let.
        do_pair.
        dosome_eq hiii.
        do_pair.
        amsts.
        repeat dunit.
        simpl.
        simpl in hi.
        simpl in Heqp2.
        repeat break_let.
        subst.
        unfold ret in *.
        do_pair.
        do_pair.
        measEventFacts.
        invc H0.
        invc H.
        +++
          do_pl_immut.
          cbn in Heqp1.
          do_pair.

          eapply IHt1 with (vmst:= {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |}) (new_vmst := {| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
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

        dosome_eq hi.
        dosome_eq hey.
        subst.
        repeat break_let.
        do_pair.
        dosome_eq hii.
        subst.
        do_pair.
        dosome_eq hii.
        dosome_eq hey.
        subst.
        repeat break_let.
        do_pair.
        dosome_eq hiii.
        do_pair.
        amsts.
        repeat dunit.
        simpl.
        simpl in hi.
        (*
        simpl in Heqp2.
        repeat break_let.
        subst.
        unfold ret in *.
        do_pair.
        do_pair. *)
        measEventFacts.
        invc H0.
        invc H.
        +++
          do_pl_immut.
          do_ba_st_const.
          df.
          dosome.
          haaa.
          
          eapply IHt1 with (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |}) (new_vmst:= {|
                                                                                                                            st_ev := st_ev2;
                                                                                                                            st_trace := st_trace1 ++ [umeas n3 0 n5 (n3 :: l)];
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
          invc H5.
          edestruct IHt2 with (vmst:={| st_ev := st_ev; st_trace := st_trace; st_pl := p; st_store := st_store |}) (new_vmst:={| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
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
        dosome_eq hi.
        dosome_eq hey.
        subst.
        repeat break_let.
        do_pair.
        do_pair.
        dosome_eq hii.
        subst.
        do_pair.
        dosome_eq hii.
        do_pair.
        dosome_eq hey.
        subst.
        repeat break_let.
        dosome_eq hiii.
        subst.
        repeat break_let.
        repeat 
          do_pair.
        dosome_eq hhhh.
        subst.
        do_pair.
        unfold extractSig in *. simpl in hey.
        destruct st_ev1; try solve_by_inversion.
        unfold ret in *.
        do_pair.
        simpl in Heqp8.
        break_match; try solve_by_inversion.
        amsts.
        do_ba_st_const.
        do_pl_immut.
        repeat dunit.
        simpl.
        
        (*
        simpl in Heqp2.
        repeat break_let.
        subst.
        unfold ret in *.
        do_pair.
        do_pair. *)
        measEventFacts.
        invc H0.
        invc H.
        +++
          do_pl_immut.
          do_ba_st_const.
          (*
          df.
          dosome.
          haaa. *)
          do_pair.
          df.
          clear IHt2.
          
          eapply IHt1 with (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |}) (new_vmst:= {|
                                                                                                                            st_ev := e;
                                                                                                                            st_trace := st_trace4 ++ [umeas n 0 n1 [encodeEv e; b]];
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
          invc H5.

    +
      dosome_eq hi.
      dosome_eq hey.
      subst.
      repeat break_let.
      do_pair.
      dosome_eq hii.
      subst.
      do_pair.
      dosome_eq hii.
      dosome_eq hey.
      subst.
      repeat break_let.
      do_pair.
      dosome_eq hiii.
      do_pair.
      amsts.
      repeat dunit.
      simpl.
      simpl in hi.
      simpl in Heqp2.
      repeat break_let.
      subst.
      unfold ret in *.
      measEventFacts.
      invc H0.
      invc H.
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


        assert (st_ev4 = st_ev2).
        {
          Check dood.
          eapply dood with (vm_st0 := {| st_ev := st_ev4; st_trace := []; st_pl := n1; st_store := [] |}).
          apply build_comp_at.
          tauto.
          tauto.
          apply Heqp2.
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
        invc H5.
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

      dosome_eq hi.
      dosome_eq hey.
      subst.
      repeat break_let.
      do_pair.
      dosome_eq hii.
      subst.
      do_pair.
      dosome_eq hii.
      dosome_eq hey.
      subst.
      repeat break_let.
      do_pair.
      dosome_eq hiii.
      do_pair.
      amsts.
      repeat dunit.
      simpl.
      simpl in hi.

      repeat break_let.
      subst.
      unfold ret in *.
      measEventFacts.
      invc H0.
      invc H.
      ++

        clear IHt2.
        (*
        df.
        dohtac.
        df. *)
        do_pl_immut.
        do_ba_st_const.
        eapply IHt1 with (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |}) (new_vmst:={| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
        eassumption.
        tauto.
        tauto.


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
        (*
        cbn in Heqp1.
        repeat break_let.
        df.
        dohtac.
        dosome.
        do_pl_immut.
        do_ba_st_const. 
        amsts.
        df. *)

        (*invc H5. *)
        edestruct IHt2 with (vmst:={| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl2; st_store := st_store |}) (new_vmst:={| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
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
        simpl in H.
        exists x.
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

           
    




Lemma app_correct' :
  forall t t' p' v_st v_st' app_comp_res_opt app_comp_res_st tr_app ev a_st e e' p et,

    t = snd (anno t' p') ->
    build_comp t v_st = (Some tt, v_st') ->
    e = st_ev v_st ->
    p = st_pl v_st ->
    e' = st_ev v_st' ->
    Ev_Shape e et ->
    app_comp_res_opt = run_appraisal_ev t p et e' a_st ->
    app_comp_res_st = fromOpt app_comp_res_opt empty_vmst ->
    tr_app = st_trace app_comp_res_st ->
    allMapped t p a_st et ->
    measEvent t p ev ->
    exists ev', In ev' tr_app /\ appEvent ev a_st ev'.
Proof.
      
      
    
  































Lemma gen_const : forall e et a o a',
    gen_appraisal_comp e et a = (o,a') ->
    a = a'.
Proof.
  induction e; intros;
    cbn in *;
    destruct et;
    try (monad_unfold; cbn in *; repeat break_match;
         repeat (find_inversion; monad_unfold);
         try (assert (a = a0) by eauto);
         subst; eauto; tauto).
Defined.



Ltac gen_st_const :=
  let tac := (eapply gen_const; eauto) in
  repeat (
      match goal with
      | [H: gen_appraisal_comp ?e ?et ?A = (?o,?B) |- _] =>
        assert_new_proof_by (A = B) tac
      (*
             destruct gen_const with (e:=ee) (et:=?et) (a:=?A) (a':=?B) (o:=?o);
             try eassumption *)
      end);
  subst.

Ltac gen_st_const' :=
  let tac := eapply gen_const; eauto in
  repeat match goal with
         | H:gen_appraisal_comp ?e ?et ?A = (?o, ?B) |- _ => assert_new_proof_by (A = B) tac
         end.

Lemma evshape_et : forall e et st,
    Ev_Shape e et ->
    evMapped et st ->
    exists res, gen_appraisal_comp e et st = (Some res, st).
Proof.
  induction e; intros;
    try evShapeFacts;
    try evMappedFacts;
    try subst'; df;
    try (edestruct IHe; [eassumption | eassumption | idtac]);
    try (edestruct IHe1; [eassumption | eassumption | idtac]);
    try subst'; df;
    try (edestruct IHe2; [eassumption | eassumption | idtac]);
    try subst'; df;
    eauto.
Defined.

Ltac do_evshape :=
  let tac := edestruct evshape_et; eauto in
  match goal with
  | [H: Ev_Shape ?e ?et,
        H2: evMapped ?et _ (*(st_aspmap ?a)*),
            H': AM_St |- _] =>
    assert_new_proof_by 
      (exists (res: VM unit), gen_appraisal_comp e et H' = (Some res, H'))
      tac ;
    clear H; clear H2
  end;
  destruct_conjs.

Ltac jkjkej :=
  match goal with
  | H:_ |- _ => erewrite H; eauto; tauto
  end.

Lemma app_some'' : forall t t' p p' e' e et (app_comp: AM (VM unit)) app_comp_res v_st v_st' (*app_comp' app_comp_res'*) a_st,
    t = snd (anno t' p') ->
    build_comp t v_st = (Some tt, v_st') ->
    e =  st_ev v_st ->
    p =  st_pl v_st ->
    e' = st_ev v_st' ->
    Ev_Shape e et ->  (* TODO: maybe don't need this *)
    allMapped t p a_st et ->
    app_comp = gen_appraisal_comp e' (eval t' p et) ->
    app_comp_res = runSt a_st app_comp ->
    exists st, (fst app_comp_res = (Some st)).
Proof.
  intros.
  subst.
  simpl in *.
  repeat find_inversion.
  subst.
  Check trace_irrel_ev'.
  Check restl'.
  Check restl'_2.
  Check suffix_prop.

  (*
  assert (exists l, tr' = tr ++ l).
  {
    eapply suffix_prop.

    reflexivity.
    eassumption.
  }
  destruct_conjs.
   *)
  
  (*
  
  destruct HHH as [blah HH].
  rewrite HH in *. *)
  (*
  assert (Ev_Shape e' (eval t' p et)). (* TODO: maybe dont' need this *)
  eapply multi_ev_eval; eauto.
  eapply restl'_2.
  reflexivity.
  eassumption. 
  

  
  erewrite announ'.
  reflexivity. *)

  (*
  rewrite <- H3 in *.
  clear H3.
  clear H. *)
  (*
  clear HH. clear blah. *)
  (*erewrite announ' in *. *)
  vmsts; simpl in *.
  generalizeEverythingElse t'.

  induction t'; intros; subst.
  
  -
    df.
    destruct a;
      simpl in *; df;
        allMappedFacts; 

        try (
            try (debound; subst');
            df;

            edestruct evshape_et; eauto;
            subst';
            df;
            eauto;
            tauto).
    (*

    + (* CPY case *) 
      inv H4;
      df;
      try evMappedFacts;
      
      try subst';    
      (* map_get_subst. *)
      
      df;
      
      try (gen_st_const);
      
      try (evShapeFacts);

      try (edestruct evshape_et;
           eauto);
      
      try (    
          repeat do_evshape;
          gen_st_const
        );
      
      repeat subst'; df; eauto. *)

  -
    df.
    dohtac.

    df.
    allMappedFacts.

    eapply IHt'.

    jkjke.
    
    apply build_comp_at.
    eassumption.
    jkjke.

  -
    (* df does too much here! *)
    cbn in *.
    repeat break_let.
    unfold snd in *.
    
    assert (alseq (p', n0) a a0 = snd (anno (lseq t'1 t'2) p')) as H.
      {
        cbn.
        repeat break_let.
        simpl.
        repeat find_inversion.
        subst'.
        df.
        eauto.
      } 
    
    assert (exists l, st_trace = st_trace0 ++ l).
    {
      eapply suffix_prop;
        eauto.
    }
    destruct_conjs.

    Check alseq_decomp.
    edestruct alseq_decomp; (* with (r:=(p',n0)). *)
      [eassumption | subst'; eapply restl'; [reflexivity | subst'; eassumption] | idtac].
         
    clear H.
    
    
    destruct_conjs.
    

    destruct (gen_appraisal_comp x (eval t'1 st_pl0 et) a_st) eqn:hi.

    gen_st_const.

    (*
    destruct IHt'1 with (a_st:=a1) (st_trace:=H3) (et:=et) (st_ev0:=st_ev0) (st_ev:=x) (st_pl0:=st_pl0) (st_trace0:=nil (A:=Ev)) (st_pl:=H) (st_store:=H6) (st_store0:=st_store0) (p':=p'). *)

    allMappedFacts.
    edestruct IHt'1;
      [jkjke | eassumption | jkjke| idtac].  

    subst.
    eapply IHt'2. (*with (st_ev0:=x) (p':=n). *)
    jkjke.
    Print do_pl_immut.
    Check pl_immut.
    do_pl_immut.
    
    eassumption.

    eapply multi_ev_eval;
      [reflexivity | jkjkej | eassumption | rewrite announ'; reflexivity].
      

    jkjke.
    assert (unanno a = t'1).
    erewrite <- announ'.
    jkjke.
    subst.
    eassumption.
    
  -
    df.

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
    
    dosome.
    
    vmsts.
    df.

    Ltac find_IHt' :=
      match goal with
      | [H1: (forall _, _),
             H2: (forall _,_) |- _] =>
          
          df;
          gen_st_const;
          
          edestruct H1;
          [jkjke | try (apply mtt); eassumption |  jkjke | idtac];
          
          subst';
          
          df;
          do_pl_immut;
          
          edestruct H2;
          [ jkjke | try (apply mtt); eassumption | jkjke | idtac];
          
          subst';
          simpl in *; subst;
          
          df;
          eauto
      end.

    allMappedFacts;
      try find_IHt'.
  -
    df.
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

    dosome.

    Ltac dooit :=
      repeat eexists;
      cbn;
      repeat break_let;
      simpl;
      repeat find_inversion;
      subst';
      df;
      reflexivity.


    
    Ltac abpar_restore_htac :=  (* TODO: move this to earlier shared Ltac library file (used in VMsemantics) *)
      let G := fresh in
      let HH := fresh in
      let HHH := fresh in
      let blah := fresh in
      let blah' := fresh in
      match goal with
      | [H2: context[abpar (?p', _) (?s0, ?s1) ?a ?a0],
             H: anno ?t'1 (S ?p') = (_,?a),
                H': anno ?t'2 _ = (_,?a0) |- _] =>
        assert ( exists r b,
                   abpar r b a a0 = snd(anno (bpar (s0,s1) t'1 t'2) p')) as G by dooit
      end;
      destruct G as [blah HH];
      destruct HH as [blah' HHH];
      dohtac;
      clear HHH;
      clear blah;
      clear blah';
      df;
      dohtac;
      df.

    abpar_restore_htac.
    
    Ltac mttac := apply mtt.
    Ltac etac := eassumption.

    Ltac datac tac1 tac2 IHt1 IHt2 :=
      df;
      gen_st_const;     
      
      edestruct IHt1;
      [jkjke; apply build_comp_par | tac1 | jkjke | idtac];
      
      subst;
      df;
      
      edestruct IHt2;
      [ jkjke; apply build_comp_par | tac2 | jkjke | idtac];

      repeat (subst'; df; subst; simpl); eauto.


    Ltac find_IHt :=
      match goal with
      | [H1: (forall _, _),
             H2: (forall _,_) |- _] =>
        try (datac mttac mttac H1 H2; tauto);
        try (datac mttac etac H1 H2; tauto);
        try (datac etac mttac H1 H2; tauto);
        try (datac etac etac H1 H2; tauto)
      end.
    
    allMappedFacts;
      find_IHt.

    (*  Maybe a hair faster...but less robust to name changes in context
    invc H5.
           
    + datac mttac mttac IHt'1 IHt'2.
    + datac mttac etac  IHt'1 IHt'2.
    + datac etac  mttac IHt'1 IHt'2.
    + datac etac  etac  IHt'1 IHt'2.
     *)
    
      
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
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
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

Print gen_appraisal_comp.
Print exec_app_comp_t.
Print exec_app_comp.
Check gen_appraisal_comp.
Check runSt.

Definition run_appraisal_ev' (t:AnnoTerm) (p:Plc) (e:Evidence) (evc:EvidenceC) : AM vm_st :=
  let evt := eval (unanno t) p e in
  app_comp <- gen_appraisal_comp evc evt ;; (* AM (VM unit) *)
  let (_, res) := runSt empty_vmst app_comp in  (* ( option () * vm_st ) *)
  ret res.

Definition run_appraisal_ev (t:AnnoTerm) (p:Plc) (e:Evidence)
           (evc:EvidenceC) (a_st:AM_St) : (option vm_st) :=
  let app_comp := run_appraisal_ev' t p e evc in
  let (o,_) := runSt a_st app_comp in
  o.

Definition run_appraisal (t:AnnoTerm) (v_st:vm_st) (et:Evidence) (a_st:AM_St) : (option vm_st) :=
  let app_comp := exec_app_comp t v_st et in
  fst (runSt a_st app_comp).

Lemma app_some : forall t t' p' res a_st v_st v_st' e e' et p,
    t = snd (anno t' p') ->
    build_comp t v_st = (Some tt, v_st') ->
    e = st_ev v_st ->
    p  = st_pl v_st ->
    e' = st_ev v_st' ->
    Ev_Shape e et ->
    allMapped t p a_st et ->
    res = run_appraisal_ev t p et e' a_st ->
    (*res = run_appraisal t v_st et a_st -> *)
    exists (st:vm_st), res = Some st.
Proof.
  intros.
  simpl in *.
  edestruct app_some'';
    try (subst; eassumption);
    try reflexivity.
  subst.
  unfold run_appraisal_ev.
  unfold run_appraisal_ev'.
  monad_unfold.
  unfold runSt in *.
  rewrite announ' in *.
  repeat break_let.
  df.
  subst.
  df.
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
    appEvent (umeas n p i args) st (umeas n' q i' (args ++ [n])).
    
Print exec_app_comp_t.
Print exec_app_comp.
Print build_app_comp.
Print allMapped.

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
  | [H: events _ _ _ |- _] => invc H
  end.
    

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

Lemma trace_cumul : forall ev evt e st st' v tr tr' p p' o o' e' o0,
    gen_appraisal_comp ev evt st = (Some v, st') ->
    v    {| st_ev := e;  st_trace := tr;  st_pl := p;  st_store := o |} =
    (o0, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o'|}) ->
    exists tr'', tr' = tr ++ tr''.
Proof.
  induction ev;
    destruct evt;
    intros;
    df; dosome; vmsts;
      try (
          df;
          dosome;
          repeat break_match;
          try solve_by_inversion;
          df;
          edestruct IHev; [eassumption | eassumption | idtac];       
          subst;
          eexists;
          try auto;
          try (rewrite app_assoc; auto);
          tauto);
      try (
          edestruct IHev1; [eassumption | eassumption | idtac];
          edestruct IHev2; [eassumption | eassumption | idtac];
          subst;
          repeat break_match;
          df;
          try (eexists; rewrite app_assoc; tauto);
          eauto;
          tauto).
  -
    df.
    exists [].
    simpl.
    rewrite app_nil_r.
    eauto.
Defined.

Lemma gen_ev_shape : forall ev evt st st' v,
    gen_appraisal_comp ev evt st = (Some v, st') ->
    Ev_Shape ev evt.
Proof.
  induction ev; destruct evt; intros;
    try (df; try econstructor; try(dosome); try solve_by_inversion; eauto; tauto).
Defined.

Lemma foofoo : forall e et e_n tr_n p_n o_n a0 a' v val e' tr' p' o' e'' tr'' p'' o'',
    gen_appraisal_comp e et a0 = (Some v, a') ->
    v {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (val, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) ->
    (exists e3 tr3 p3 o3,
        v {| st_ev := e_n; st_trace := tr_n; st_pl := p_n; st_store := o_n |} =
        (val, {| st_ev := e3; st_trace := tr3; st_pl := p3; st_store := o3 |})).
Proof.
  induction e;
    destruct et; intros;
      try (df; eauto);
      try
        ( dosome;
          edestruct IHe; [eassumption | eassumption | idtac];
          destruct_conjs;
          repeat eexists;
          try eassumption; 
          rewrite <- H2;
          rewrite Heqp2;
          reflexivity);
      try
        ( dosome;
          vmsts;
          edestruct IHe1; [eassumption | apply Heqp1 | idtac];
          edestruct IHe2; [eassumption | apply Heqp2 | idtac];
          destruct_conjs;
          rewrite H4 in *;
          df;
          rewrite H7 in *;
          df;

          break_match_goal;
          df; eauto;
          tauto).
Defined.

Lemma dodo : forall e e' e'' p' p'' o' o'' tr' tr'' et v0 a a' val, 
    (* build_comp a0
            {|
            st_ev := splitEv s0 e;
            st_trace := tr;
            st_pl := p;
            st_store := o |} =
      (Some tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) -> *)

    gen_appraisal_comp e et a = (Some v0, a') ->
    (*Ev_Shape e et -> *)
    
    v0 {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (val, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) ->
    val = Some tt.
Proof.
  induction e; 
    destruct et; intros;
      df;
      try tauto;
      dosome; df; vmsts;
        try
          ( try (break_match; try solve_by_inversion);
            edestruct foofoo; [eassumption | eassumption | idtac];
            destruct_conjs;
            
            eapply IHe;
            eassumption);
        try
          ( edestruct foofoo; [apply Heqp | eassumption | idtac];
            edestruct foofoo; [apply Heqp0 | eassumption | idtac];
            destruct_conjs;

            rewrite H4 in *;
            df;
            rewrite H7 in *;
            df;

            (*inv H0. *)

            assert (o = Some tt)
              by ( eapply IHe1;
                   eassumption);

            subst;
            df;

            eapply IHe2;
            eassumption).
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
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
Defined.



Lemma gen_ev_mapped : forall e et a x a',
    gen_appraisal_comp e et a = (Some x,a') ->
    evMapped et a.
Proof.
  induction e; destruct et; intros;
    try (df; econstructor; tauto);
    try (df; dosome; econstructor; eauto; tauto);
    try (df;
         dosome;
         haaa;
         econstructor;
         [reflexivity | eauto | eexists; econstructor; eauto];
         tauto);
    try (econstructor;
         cbn in *;
         monad_unfold;
         ff;
         dosome;
         gen_st_const;
         eauto;
         tauto).
Defined.

Lemma inEvApp{A:Type} : forall (ev:A) l1 l2,
        In ev (l1 ++ l2) ->
        In ev l1 \/ In ev l2.
Proof.
  intros.
  Search In.
  apply in_app_or.
  eauto.
Defined.

Print list.
Lemma lista{A:Type} : forall (y x: list A),
    x = x ++ y ->
    y = [].
Proof.
  intros.
  assert (x ++ [] = x).
  rewrite app_nil_r.
  reflexivity.
  rewrite <- H0 in H at 1.
  eapply app_inv_head; eauto.
Defined.

Ltac do_cumul :=
  let tac := (eapply trace_cumul; eauto) in
  repeat
    match goal with
    | [
      H: _ {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}) |- _] =>
      assert_new_proof_by (exists tr'' : list Ev, tr1' = tr1 ++ tr'') tac
    end;
  destruct_conjs.



Ltac dof :=
  let tac t := (eapply app_inv_head; rewrite <- app_assoc in t; eauto) in
  match goal with
  | [H: ?tr1 ++ ?x1 = (?tr1 ++ ?um) ++ ?mu |- _] =>
    assert (x1 = um ++ mu) by (tac H); subst; clear H
  end.

Lemma gogo' : forall e et a a' v1 e1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0 x1,
    gen_appraisal_comp e et a = (Some v1, a') ->
    v1 {| st_ev := e1; st_trace := tr1; st_pl := p1; st_store := o1 |} =
    (Some tt, {| st_ev := e1'; st_trace := tr1 ++ x1; st_pl := p1'; st_store := o1' |}) ->
    v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
    (Some tt, {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) ->
    x0 = x1.
Proof.
  intros.
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

Lemma gogo : forall e et a a' v1 e1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0,
    gen_appraisal_comp e et a = (Some v1, a') ->
    v1 {| st_ev := e1; st_trace := []; st_pl := p1; st_store := o1 |} =
    (Some tt, {| st_ev := e1'; st_trace := tr1; st_pl := p1'; st_store := o1' |}) ->
    v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
    (Some tt, {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) ->
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


Check gogo'.
(*
gogo'
     : forall (e : EvidenceC) (et : Evidence) (a a' : AM_St) (v1 : VM unit) (e1 e1' : EvidenceC) (p1 p1' : nat) (o1 o1' : ev_store)
         (e2 e2' : EvidenceC) (tr2 : list Ev) (p2 p2' : nat) (o2 o2' : ev_store) (tr1 x0 x1 : list Ev),
       gen_appraisal_comp e et a = (Some v1, a') ->
       v1 {| st_ev := e1; st_trace := tr1; st_pl := p1; st_store := o1 |} =
       (Some tt, {| st_ev := e1'; st_trace := tr1 ++ x1; st_pl := p1'; st_store := o1' |}) ->
       v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
       (Some tt, {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) -> x0 = x1
*)

Ltac do_gogo' :=
  let tac := (eapply gogo'; eauto) in
  repeat 
  match goal with
  | [H1: ?v {| st_ev := ?e1; st_trace := ?tr1; st_pl := ?p1; st_store := ?o1 |} =
         (_, {| st_ev := ?e1'; st_trace := ?tr1 ++ ?tr1'; st_pl := ?p1'; st_store := ?o1' |}),
         H2: ?v {| st_ev := ?e2; st_trace := ?tr2; st_pl := ?p2; st_store := ?o2 |} =
             (_, {| st_ev := ?e2'; st_trace := ?tr2 ++ ?tr2'; st_pl := ?p2'; st_store := ?o2' |}),
             H3: gen_appraisal_comp ?e ?et ?a = (Some ?v1, ?a') |- _] =>
    pose_new_proof (gogo' e et a a' v1 e1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 tr2' tr1' H3 H1 H2 )

      (*(tr1' = tr2') tac *)
  end.

Ltac destr_or :=
  match goal with
  | [H: _ \/ _ |- _] => destruct H
  end.


Lemma in_singleton{A:Type} : forall (ev ev':A),
    In ev [ev'] -> ev = ev'.
Proof.
  intros.
  inv H.
  reflexivity.
  solve_by_inversion.
Defined.

Ltac in_simpl :=
  match goal with
  | [H: In ?ev [?ev'] |- _] =>
    assert (ev = ev') by (eapply in_singleton; eauto)
  end; subst.

Ltac fafa h := (eapply trace_cumul; [apply h | eauto]).

Print assert_new_proof_by.

Ltac do_cumul' :=
  let tac h := fafa h in

  match goal with
  | [H: ?v {| st_ev := ?e; st_trace := ?tr1; st_pl := ?p; st_store := ?o |} = (?o0, {| st_ev := ?e'; st_trace := ?tr1'; st_pl := ?p'; st_store := ?o' |}),
        H2: gen_appraisal_comp ?e1 ?et1 ?a0 = (Some ?v, ?a0')
     |- _] => pose_new_proof
              ( trace_cumul e1 et1 e a0 a0' v tr1 tr1' p p' o o' e' o0 H2 H)


              (*(exists tr'' : list Ev, tr1' = tr1 ++ tr'') *)
              
  end.

Lemma gen_comp_eval : forall e t p' et a x0,
    gen_appraisal_comp e (eval t p' et) a = (Some x0, a) ->
    exists e' x0',
      gen_appraisal_comp e' et a = (Some x0', a).
Proof.
Admitted.

Lemma asdd : forall a e' p et a_st a_st' x0 p' t' ,
    a = snd (anno t' p') ->
    gen_appraisal_comp e' (eval (unanno a) p et) a_st = (Some x0, a_st') ->
    allMapped a p a_st et.
Proof.
Admitted.

Ltac do_pl_immut' :=
  let tac := (symmetry; erewrite <- pl_immut in *; jkjk') in
  repeat
    match goal with
    | H:build_comp _ {| st_ev := _; st_trace := _; st_pl := ?p; st_store := _ |} =
        (_, {| st_ev := _; st_trace := _; st_pl := ?p'; st_store := _ |}) |- _ => assert_new_proof_by (p = p') tac
    end.


(*
Lemma gen_lseq_decomp :
  forall a1 a0 et p p'' p' e e' ee eee  st_trace3 st_trace4 o tr tr' o' pp ppp oo ooo a_st x0 x ev' t' n e'' tr'' o'',
    a1 = snd (anno t' n) ->
    build_comp a0 {| st_ev := e; st_trace := tr; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) -> 
    build_comp a1 {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) -> 
    gen_appraisal_comp e'' (eval (unanno a1) p' (eval (unanno a0) p et)) a_st = (Some x0, a_st) ->
   (* Ev_Shape e et -> (* TODO: need this? *) *)
    x0 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |} =
    (Some tt, {| st_ev := ee; st_trace := st_trace3; st_pl := pp; st_store := oo |}) ->
    gen_appraisal_comp e' (eval (unanno a0) p et) a_st = (Some x, a_st) ->
    x {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |} =
    (Some tt, {| st_ev := eee; st_trace := st_trace4; st_pl := ppp; st_store := ooo |}) ->
    In ev' st_trace4 -> In ev' st_trace3.
Proof.
  intros.
  (*
  assert (Ev_Shape e' (eval (unanno a1) p' et)).
  eapply gen_ev_shape; eauto.
  assert (Ev_Shape e et).
  eapply gen_ev_shape; eauto. *)
  generalizeEverythingElse a1.
  intros a0.
  intros et.
  intros p.
  induction a1; destruct (eval (unanno a0) p et) eqn: hey; intros.

  -
        destruct a;
      try (df; repeat evShapeFacts; df; eauto).
    solve_by_inversion.
    solve_by_inversion.
    

  (*
    try
      ( df;
        dohtac;
        df;
        destruct t';
        try (cbn in *;
             repeat break_let;
             cbn in *;
             try solve_by_inversion;
             invc H);
        df;
        eapply IHa1;
        [jkjke | apply build_comp_at | eassumption
         | eassumption | eassumption | eassumption
         | eassumption | eassumption | eassumption]).
   *)
  
  do_pl_immut.
  rewrite hey in *.
Admitted.
*)

Lemma gen_lseq_decomp :
  forall a1 et e e' ee eee  st_trace3 st_trace4 o p p' tr tr' o' pp ppp oo ooo a_st a a2 x0 x ev' t' n,
    a1 = snd (anno t' n) ->
    build_comp a1 {| st_ev := e; st_trace := tr; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) -> 
    (*build_comp a1 {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) -> *)
    gen_appraisal_comp e' (eval (unanno a1) p' et (*(eval (unanno a0) p et)*)) a_st = (Some x0, a) ->
   (* Ev_Shape e et -> (* TODO: need this? *) *)
    x0 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |} =
    (Some tt, {| st_ev := ee; st_trace := st_trace3; st_pl := pp; st_store := oo |}) ->
    gen_appraisal_comp e et (*(eval (unanno a0) p et)*) a_st = (Some x, a2) ->
    x {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |} =
    (Some tt, {| st_ev := eee; st_trace := st_trace4; st_pl := ppp; st_store := ooo |}) ->
    In ev' st_trace4 -> In ev' st_trace3.
Proof.

  intros.
  assert (Ev_Shape e' (eval (unanno a1) p' et)).
  eapply gen_ev_shape; eauto.
  assert (Ev_Shape e et).
  eapply gen_ev_shape; eauto.
  generalizeEverythingElse a1.
  induction a1; destruct et; intros;
    try
      ( df;
        dohtac;
        df;
        destruct t';
        try (cbn in *;
             repeat break_let;
             cbn in *;
             try solve_by_inversion;
             invc H);
        df;
        eapply IHa1;
        [jkjke | apply build_comp_at | eassumption
         | eassumption | eassumption | eassumption
         | eassumption | eassumption | eassumption]).

    (*
    try
      (
      destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      dosome;
      haaa;

      subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      haaa;

      do_cumul;
      subst;

      do_gogo';
    
      (*
      assert (H2 = H4) by (eapply gogo'; eauto); subst;

      apply in_app_or in H5;
      inv H5;
        [ apply in_or_app;
          left;
          unfold In;
          inv H2;
          try solve_by_inversion;
          right; left; tauto
        | apply in_or_app;
          right;
          eassumption]).
       *)
     
      df;
      destr_or; eauto;
      tauto);
      tauto).
     *)
  











  
  -
    destruct a;
      try (df; repeat evShapeFacts; df; eauto).
    solve_by_inversion.
    solve_by_inversion.

  -
        destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      try dosome;
      try haaa;

      try subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      try haaa;

      df;
        vmsts;
        gen_st_const;

      repeat do_cumul';
      destruct_conjs;
      subst;

      do_gogo';
      subst;
     
      df;
      try destr_or; eauto);
      try solve_by_inversion.
  -
        destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      try dosome;
      try haaa;

      try subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      try haaa;

      df;
        vmsts;
        gen_st_const;

      repeat do_cumul';
      destruct_conjs;
      subst;

      do_gogo';
      subst;
     
      df;
      try destr_or; eauto);
      try solve_by_inversion.
  -
        destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      try dosome;
      try haaa;

      try subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      try haaa;

      df;
        vmsts;
        gen_st_const;

      repeat do_cumul';
      destruct_conjs;
      subst;

      do_gogo';
      subst;
     
      df;
      try destr_or; eauto);
      try solve_by_inversion.
  -
        destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      try dosome;
      try haaa;

      try subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      try haaa;

      df;
        vmsts;
        gen_st_const;

      repeat do_cumul';
      destruct_conjs;
      subst;

      do_gogo';
      subst;
     
      df;
      try destr_or; eauto);
      try solve_by_inversion.
  -
        destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      try dosome;
      try haaa;

      try subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      try haaa;

      df;
        vmsts;
        gen_st_const;

      repeat do_cumul';
      destruct_conjs;
      subst;

      do_gogo';
      subst;
     
      df;
      try destr_or; eauto);
      try solve_by_inversion.
  -
        destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      try dosome;
      try haaa;

      try subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      try haaa;

      df;
        vmsts;
        gen_st_const;

      repeat do_cumul';
      destruct_conjs;
      subst;

      do_gogo';
      subst;
     
      df;
      try destr_or; eauto);
      try solve_by_inversion.
        (*
  -
        destruct a;

      try ( df; dosome; repeat (subst'; df); eauto; tauto);
      try (
          
      df;
      vmsts;
      gen_st_const;
      
      try dosome;
      try haaa;

      try subst'';
      df;

      repeat evShapeFacts;
      df;

      dosome;
      try haaa;

      df;
        vmsts;
        gen_st_const;

      repeat do_cumul';
      destruct_conjs;
      subst;

      do_gogo';
      subst;
     
      df;
      try destr_or; eauto);
      try solve_by_inversion.












(*
  -

    cbn in *.
    monad_unfold.
    repeat break_let.
    df.
    dosome.
    df.
    vmsts.

    invc H7.
    cbn in *.
    monad_unfold.
    df.
    dosome.
    haaa.
   
    inv H6.
    inv H6.

    admit.
 *)
        
    
  -
    
    cbn in *.
    monad_unfold.
    repeat break_let.
    df.
    dosome.
    df.
    vmsts.

    assert (exists t' p', a1_1 = snd (anno t' p')). admit.
    destruct_conjs.

    destruct (gen_appraisal_comp st_ev (eval (unanno a1_1) p' (uu n l n0 et)) a_st) eqn:hoho.
    assert (exists vv, o0 = Some vv).
    {
      edestruct app_some''.
      eassumption.
      eassumption.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      eassumption.
      simpl.
      Print do_pl_immut.
      assert (allMapped a1_1 p a_st (uu n l n0 et)).
      {
        Check dodo.
        Check foofoo.


        

        repeat gen_st_const'.
        rewrite H11 in *; clear H11.
        rewrite H9 in *; clear H9.
        rewrite H10 in *; clear H10.
        
        edestruct gen_comp_eval.
        apply H1.
        destruct_conjs.

        edestruct suffix_prop.
        rewrite <- H8.
        reflexivity.
        eassumption.
        rewrite H11 in *; clear H11.
        edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1_1) p'  (uu n l n0 et))).
        eapply multi_ev_eval.
        rewrite <- H8.
        reflexivity.
        eapply restl'.
        eassumption.
        eassumption.
        eassumption.
        do_pl_immut.
        reflexivity.

        (*eapply asas.
        gen_st_const.
        apply H0. *)
        Check gen_ev_mapped.
        eapply gen_ev_mapped.
        eassumption.


        
        
        repeat gen_st_const'.
        (*
        rewrite H9 in *. 
        df. *)
        

        (*
        eapply asdd.
        do_pl_immut.
        
        eassumption. *)

        


          do_pl_immut.
          eapply asdd; eauto.
      }
      
      apply H9.
     
      reflexivity.
      reflexivity.
      simpl in *.
      unfold runSt in *.
      do_pl_immut.
      rewrite announ' in *.
      rewrite hoho in *.
      simpl in *.
      subst.
      eauto.
    }
    
    destruct_conjs.
    subst.

    destruct (H9 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hei.
    assert (o0 = Some tt).
    {
      vmsts.
      Check app_some''.
      eapply dodo.
      eapply hoho.
      apply hei.
    }
    
    
    subst.
    vmsts.
    

    (*
    assert (exists t' p', a1_2 = snd (anno t' p')). admit.
    destruct_conjs.
     *)
    
    eapply IHa1_2.
    (*
    rewrite H11.
    cbn.
    simpl.
    break_let. *)
    admit.

    
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply IHa1_1.
    admit.
    eassumption.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    edestruct suffix_prop.
    reflexivity.
    apply Heqp0.
    Check evshape_et.
    Check gen_ev_shape.
    eapply gen_ev_shape.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eapply gen_ev_shape.
    eassumption.
  -
  
    
    cbn in *.
    monad_unfold.
    repeat break_let.
    df.
    dosome.
    df.
    vmsts.

    assert (exists t' p', a1_1 = snd (anno t' p')). admit.
    destruct_conjs.

    destruct (gen_appraisal_comp st_ev (eval (unanno a1_1) p' (gg n et)) a_st) eqn:hoho.
    assert (exists vv, o0 = Some vv).
    {
      edestruct app_some''.
      eassumption.
      eassumption.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      eassumption.
      simpl.
      Print do_pl_immut.
      assert (allMapped a1_1 p a_st (gg n et)).
      {
        Check dodo.
        Check foofoo.


        

        repeat gen_st_const'.
        rewrite H11 in *; clear H11.
        rewrite H9 in *; clear H9.
        rewrite H10 in *; clear H10.
        
        edestruct gen_comp_eval.
        apply H1.
        destruct_conjs.

        edestruct suffix_prop.
        rewrite <- H8.
        reflexivity.
        eassumption.
        rewrite H11 in *; clear H11.
        edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1_1) p'  (gg n et))).
        eapply multi_ev_eval.
        rewrite <- H8.
        reflexivity.
        eapply restl'.
        eassumption.
        eassumption.
        eassumption.
        do_pl_immut.
        reflexivity.

        (*eapply asas.
        gen_st_const.
        apply H0. *)
        Check gen_ev_mapped.
        eapply gen_ev_mapped.
        eassumption.


        
        
        repeat gen_st_const'.
        (*
        rewrite H9 in *. 
        df. *)
        

        (*
        eapply asdd.
        do_pl_immut.
        
        eassumption. *)

        


          do_pl_immut.
          eapply asdd; eauto.
      }
      
      apply H9.
     
      reflexivity.
      reflexivity.
      simpl in *.
      unfold runSt in *.
      do_pl_immut.
      rewrite announ' in *.
      rewrite hoho in *.
      simpl in *.
      subst.
      eauto.
    }
    
    destruct_conjs.
    subst.

    destruct (H9 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hei.
    assert (o0 = Some tt).
    {
      vmsts.
      Check app_some''.
      eapply dodo.
      eapply hoho.
      apply hei.
    }
    
    
    subst.
    vmsts.
    

    (*
    assert (exists t' p', a1_2 = snd (anno t' p')). admit.
    destruct_conjs.
     *)
    
    eapply IHa1_2.
    (*
    rewrite H11.
    cbn.
    simpl.
    break_let. *)
    admit.

    
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply IHa1_1.
    admit.
    eassumption.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    edestruct suffix_prop.
    reflexivity.
    apply Heqp0.
    Check evshape_et.
    Check gen_ev_shape.
    eapply gen_ev_shape.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eapply gen_ev_shape.
    eassumption.

  -
    
    cbn in *.
    monad_unfold.
    repeat break_let.
    df.
    dosome.
    df.
    vmsts.

    assert (exists t' p', a1_1 = snd (anno t' p')). admit.
    destruct_conjs.

    destruct (gen_appraisal_comp st_ev (eval (unanno a1_1) p' (hh n et)) a_st) eqn:hoho.
    assert (exists vv, o0 = Some vv).
    {
      edestruct app_some''.
      eassumption.
      eassumption.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      eassumption.
      simpl.
      Print do_pl_immut.
      assert (allMapped a1_1 p a_st (hh n et)).
      {
        Check dodo.
        Check foofoo.


        

        repeat gen_st_const'.
        rewrite H11 in *; clear H11.
        rewrite H9 in *; clear H9.
        rewrite H10 in *; clear H10.
        
        edestruct gen_comp_eval.
        apply H1.
        destruct_conjs.

        edestruct suffix_prop.
        rewrite <- H8.
        reflexivity.
        eassumption.
        rewrite H11 in *; clear H11.
        edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1_1) p'  (hh n et))).
        eapply multi_ev_eval.
        rewrite <- H8.
        reflexivity.
        eapply restl'.
        eassumption.
        eassumption.
        eassumption.
        do_pl_immut.
        reflexivity.

        (*eapply asas.
        gen_st_const.
        apply H0. *)
        Check gen_ev_mapped.
        eapply gen_ev_mapped.
        eassumption.


        
        
        repeat gen_st_const'.
        (*
        rewrite H9 in *. 
        df. *)
        

        (*
        eapply asdd.
        do_pl_immut.
        
        eassumption. *)

        


          do_pl_immut.
          eapply asdd; eauto.
      }
      
      apply H9.
     
      reflexivity.
      reflexivity.
      simpl in *.
      unfold runSt in *.
      do_pl_immut.
      rewrite announ' in *.
      rewrite hoho in *.
      simpl in *.
      subst.
      eauto.
    }
    
    destruct_conjs.
    subst.

    destruct (H9 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hei.
    assert (o0 = Some tt).
    {
      vmsts.
      Check app_some''.
      eapply dodo.
      eapply hoho.
      apply hei.
    }
    
    
    subst.
    vmsts.
    

    (*
    assert (exists t' p', a1_2 = snd (anno t' p')). admit.
    destruct_conjs.
     *)
    
    eapply IHa1_2.
    (*
    rewrite H11.
    cbn.
    simpl.
    break_let. *)
    admit.

    
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply IHa1_1.
    admit.
    eassumption.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    edestruct suffix_prop.
    reflexivity.
    apply Heqp0.
    Check evshape_et.
    Check gen_ev_shape.
    eapply gen_ev_shape.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eapply gen_ev_shape.
    eassumption.

  -
        cbn in *.
    monad_unfold.
    repeat break_let.
    df.
    dosome.
    df.
    vmsts.

    assert (exists t' p', a1_1 = snd (anno t' p')). admit.
    destruct_conjs.

    destruct (gen_appraisal_comp st_ev (eval (unanno a1_1) p' (nn n et)) a_st) eqn:hoho.
    assert (exists vv, o0 = Some vv).
    {
      edestruct app_some''.
      eassumption.
      eassumption.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      eassumption.
      simpl.
      Print do_pl_immut.
      assert (allMapped a1_1 p a_st (nn n et)).
      {
        Check dodo.
        Check foofoo.


        

        repeat gen_st_const'.
        rewrite H11 in *; clear H11.
        rewrite H9 in *; clear H9.
        rewrite H10 in *; clear H10.
        
        edestruct gen_comp_eval.
        apply H1.
        destruct_conjs.

        edestruct suffix_prop.
        rewrite <- H8.
        reflexivity.
        eassumption.
        rewrite H11 in *; clear H11.
        edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1_1) p'  (nn n et))).
        eapply multi_ev_eval.
        rewrite <- H8.
        reflexivity.
        eapply restl'.
        eassumption.
        eassumption.
        eassumption.
        do_pl_immut.
        reflexivity.

        (*eapply asas.
        gen_st_const.
        apply H0. *)
        Check gen_ev_mapped.
        eapply gen_ev_mapped.
        eassumption.


        
        
        repeat gen_st_const'.
        (*
        rewrite H9 in *. 
        df. *)
        

        (*
        eapply asdd.
        do_pl_immut.
        
        eassumption. *)

        


          do_pl_immut.
          eapply asdd; eauto.
      }
      
      apply H9.
     
      reflexivity.
      reflexivity.
      simpl in *.
      unfold runSt in *.
      do_pl_immut.
      rewrite announ' in *.
      rewrite hoho in *.
      simpl in *.
      subst.
      eauto.
    }
    
    destruct_conjs.
    subst.

    destruct (H9 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hei.
    assert (o0 = Some tt).
    {
      vmsts.
      Check app_some''.
      eapply dodo.
      eapply hoho.
      apply hei.
    }
    
    
    subst.
    vmsts.
    

    (*
    assert (exists t' p', a1_2 = snd (anno t' p')). admit.
    destruct_conjs.
     *)
    
    eapply IHa1_2.
    (*
    rewrite H11.
    cbn.
    simpl.
    break_let. *)
    admit.

    
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply IHa1_1.
    admit.
    eassumption.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    edestruct suffix_prop.
    reflexivity.
    apply Heqp0.
    Check evshape_et.
    Check gen_ev_shape.
    eapply gen_ev_shape.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eapply gen_ev_shape.
    eassumption.
  -
    cbn in *.
    monad_unfold.
    repeat break_let.
    df.
    dosome.
    df.
    vmsts.

    assert (exists t' p', a1_1 = snd (anno t' p')). admit.
    destruct_conjs.

    destruct (gen_appraisal_comp st_ev (eval (unanno a1_1) p' (ss et1 et2)) a_st) eqn:hoho.
    assert (exists vv, o0 = Some vv).
    {
      edestruct app_some''.
      eassumption.
      eassumption.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      eassumption.
      simpl.
      Print do_pl_immut.
      assert (allMapped a1_1 p a_st (ss et1 et2)).
      {
        Check dodo.
        Check foofoo.


        

        repeat gen_st_const'.
        rewrite H11 in *; clear H11.
        rewrite H9 in *; clear H9.
        rewrite H10 in *; clear H10.
        
        edestruct gen_comp_eval.
        apply H1.
        destruct_conjs.

        edestruct suffix_prop.
        rewrite <- H8.
        reflexivity.
        eassumption.
        rewrite H11 in *; clear H11.
        edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1_1) p'  (ss et1 et2))).
        eapply multi_ev_eval.
        rewrite <- H8.
        reflexivity.
        eapply restl'.
        eassumption.
        eassumption.
        eassumption.
        do_pl_immut.
        reflexivity.

        (*eapply asas.
        gen_st_const.
        apply H0. *)
        Check gen_ev_mapped.
        eapply gen_ev_mapped.
        eassumption.


        
        
        repeat gen_st_const'.
        (*
        rewrite H9 in *. 
        df. *)
        

        (*
        eapply asdd.
        do_pl_immut.
        
        eassumption. *)

        


          do_pl_immut.
          eapply asdd; eauto.
      }
      
      apply H9.
     
      reflexivity.
      reflexivity.
      simpl in *.
      unfold runSt in *.
      do_pl_immut.
      rewrite announ' in *.
      rewrite hoho in *.
      simpl in *.
      subst.
      eauto.
    }
    
    destruct_conjs.
    subst.

    destruct (H9 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hei.
    assert (o0 = Some tt).
    {
      vmsts.
      Check app_some''.
      eapply dodo.
      eapply hoho.
      apply hei.
    }
    
    
    subst.
    vmsts.
    

    (*
    assert (exists t' p', a1_2 = snd (anno t' p')). admit.
    destruct_conjs.
     *)
    
    eapply IHa1_2.
    (*
    rewrite H11.
    cbn.
    simpl.
    break_let. *)
    admit.

    
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply IHa1_1.
    admit.
    eassumption.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    edestruct suffix_prop.
    reflexivity.
    apply Heqp0.
    Check evshape_et.
    Check gen_ev_shape.
    eapply gen_ev_shape.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eapply gen_ev_shape.
    eassumption.
  -
        cbn in *.
    monad_unfold.
    repeat break_let.
    df.
    dosome.
    df.
    vmsts.

    assert (exists t' p', a1_1 = snd (anno t' p')). admit.
    destruct_conjs.

    destruct (gen_appraisal_comp st_ev (eval (unanno a1_1) p' (Term.pp et1 et2)) a_st) eqn:hoho.
    assert (exists vv, o0 = Some vv).
    {
      edestruct app_some''.
      eassumption.
      eassumption.
      reflexivity.
      reflexivity.
      reflexivity.
      simpl.
      eassumption.
      simpl.
      Print do_pl_immut.
      assert (allMapped a1_1 p a_st (Term.pp et1 et2)).
      {
        Check dodo.
        Check foofoo.


        

        repeat gen_st_const'.
        rewrite H11 in *; clear H11.
        rewrite H9 in *; clear H9.
        rewrite H10 in *; clear H10.
        
        edestruct gen_comp_eval.
        apply H1.
        destruct_conjs.

        edestruct suffix_prop.
        rewrite <- H8.
        reflexivity.
        eassumption.
        rewrite H11 in *; clear H11.
        edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1_1) p'  (Term.pp et1 et2))).
        eapply multi_ev_eval.
        rewrite <- H8.
        reflexivity.
        eapply restl'.
        eassumption.
        eassumption.
        eassumption.
        do_pl_immut.
        reflexivity.

        (*eapply asas.
        gen_st_const.
        apply H0. *)
        Check gen_ev_mapped.
        eapply gen_ev_mapped.
        eassumption.


        
        
        repeat gen_st_const'.
        (*
        rewrite H9 in *. 
        df. *)
        

        (*
        eapply asdd.
        do_pl_immut.
        
        eassumption. *)

        


          do_pl_immut.
          eapply asdd; eauto.
      }
      
      apply H9.
     
      reflexivity.
      reflexivity.
      simpl in *.
      unfold runSt in *.
      do_pl_immut.
      rewrite announ' in *.
      rewrite hoho in *.
      simpl in *.
      subst.
      eauto.
    }
    
    destruct_conjs.
    subst.

    destruct (H9 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hei.
    assert (o0 = Some tt).
    {
      vmsts.
      Check app_some''.
      eapply dodo.
      eapply hoho.
      apply hei.
    }
    
    
    subst.
    vmsts.
    

    (*
    assert (exists t' p', a1_2 = snd (anno t' p')). admit.
    destruct_conjs.
     *)
    
    eapply IHa1_2.
    (*
    rewrite H11.
    cbn.
    simpl.
    break_let. *)
    admit.

    
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply IHa1_1.
    admit.
    eassumption.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    edestruct suffix_prop.
    reflexivity.
    apply Heqp0.
    Check evshape_et.
    Check gen_ev_shape.
    eapply gen_ev_shape.
    do_pl_immut.
    eassumption.
    eassumption.
    eassumption.
    eapply gen_ev_shape.
    eassumption.
  -

    repeat evShapeFacts.
    df.
    dosome.
  -
    repeat evShapeFacts.
    df.
    dosome.
    vmsts.
    haaa.
    vmsts.
    df.
    repeat evShapeFacts.

    gen_st_const'.
    subst.

    repeat do_cumul'.
    destruct_conjs.
    subst.
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
      
      
    
      

      
    























    










(*

  
  induction e''; intros.
  -
    assert (Ev_Shape mtc (eval (unanno a1) p' et)).
    
    eapply gen_ev_shape; eauto.
    inv H3.
    cbn in *.
    subst.
    rewrite <- H4 in *.
    monad_unfold.
    df.
    Lemma hfhf : forall a1 p' et,
      mt = eval (unanno a1) p' et ->
      et = mt.
    Proof.
      induction a1; intros.
      -
        destruct a;
          cbn in *;
          try solve_by_inversion.
      -
        cbn in *.
        eauto.
      -
        cbn in *.
        assert ((eval (unanno a1_1) p' et) = mt).
        eauto.
        subst.
        rewrite H0 in *.
        eauto.

      -
        cbn in *.
        inv H.
      -
        cbn in *.
        inv H.
    Defined.

    assert (et = mt).
    eapply hfhf. eauto.
    subst.
    assert (Ev_Shape e' mt).
    eapply gen_ev_shape; eauto.
    invc H.
    cbn in *.
    monad_unfold.
    df.
    eauto.
  -

    assert (Ev_Shape (uuc n n0 e'') (eval (unanno a1) p' et)).
    eapply gen_ev_shape; eauto.
    invc H3.
    rewrite <- H8 in *.
    df.
    dosome.
    repeat break_match;
      try solve_by_inversion.
    df.
    assert (et = et0).
    {
      admit.
    }
    subst.
    

    edestruct IHe''.
    eassumption.
    
    
    
 
   *) 

*)
    
  
Admitted.
      
Lemma app_correct' :
  forall t t' p' v_st v_st' app_comp_res_opt app_comp_res_st tr_app ev a_st e e' p et,

    t = snd (anno t' p') ->
    build_comp t v_st = (Some tt, v_st') ->
    e = st_ev v_st ->
    p = st_pl v_st ->
    e' = st_ev v_st' ->
    Ev_Shape e et ->
    app_comp_res_opt = run_appraisal_ev t p et e' a_st ->
    app_comp_res_st = fromOpt app_comp_res_opt empty_vmst ->
    tr_app = st_trace app_comp_res_st ->
    allMapped t p a_st et ->
    measEvent t p ev ->
    exists ev', In ev' tr_app /\ appEvent ev a_st ev'.
Proof.
  intros.
  edestruct app_some; try eassumption.
  subst.
  Print subst'.
  rewrite H10.
  cbn.
  unfold run_appraisal_ev in *.
  unfold run_appraisal_ev' in *.
  unfold runSt in *.
  monad_unfold.
  repeat break_let.
  repeat find_inversion.
  subst.
  repeat break_match; try solve_by_inversion.
  repeat find_inversion.
  Check announ'.
  
  rewrite announ' in *.
  simpl in *.
  unfold empty_vmst in *.
  vmsts.
  simpl in *.
  repeat find_inversion.

  (*
  assert (snd (runSt empty_vmst v) = x).
  congruence.
  clear H8.
  rewrite H. *)
  generalizeEverythingElse t'.
  

  induction t'; intros.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    destruct a;
      df;
      try (
          measEventFacts;
          invEvents;
          evEventFacts; tauto).

    +
      df.
      dosome.
      (*
      cbn in *.
      repeat break_let.
      repeat find_inversion.
      monad_unfold.
      monad_unfold.
      repeat find_inversion.
      cbn in *.
      repeat break_let.
      destruct o;
        try solve_by_inversion.
      repeat break_let.
      repeat find_inversion.
      destruct o0;
        try solve_by_inversion.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      simpl in *. *)
      measEventFacts.
      invEvents.
      evEventFacts.
      allMappedFacts.
      (*
      invc H9.
      invc H.
      invc H0.
      invc H8. *)
      destruct_conjs.
      inv H.
      subst'.
      df.
     
      cbn in *.
      (*
      rewrite H0 in *. 
      
      monad_unfold.
      repeat find_inversion.
      repeat break_let.
      repeat find_inversion.
      (*
      destruct o1;
        try solve_by_inversion.
      repeat find_inversion. *)
      unfold runSt.
      repeat find_inversion.
      repeat break_let.
      simpl in *.
      repeat find_inversion. *)
      vmsts.
      repeat find_inversion.
      unfold empty_vmst in *.
      repeat find_inversion.
      simpl in *.
      exists (umeas 0 st_pl0 n0 (l ++ [p'])).
      split.
      ++



      edestruct trace_cumul; eauto.
      (*
      eassumption.
      eassumption. *)
      subst.
      econstructor.
      reflexivity.
      ++
        
      econstructor.
      reflexivity.
      eassumption.


      (*
    +





      edestruct trace_cumul.
      eassumption.
      eassumption.
      subst.
      econstructor.
      reflexivity. *)

  -
    df.
    (*
    cbn in *.
    repeat break_let.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold run_vm in *. *)
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    df.
    (*
    repeat find_inversion.
    monad_unfold.
    cbn in *.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    repeat find_inversion. *)
    dohtac.
    repeat find_inversion.
    simpl in *.
    allMappedFacts.
    measEventFacts.
    invEvents; try solve_by_inversion.

    (*
    invc H8.
    invc H9.

    invc H;
      try solve_by_inversion. *)
    

    edestruct IHt'.
    apply build_comp_at.
    eassumption.
    jkjke.
    (*
    
    rewrite Heqp.
    simpl.
    eassumption. *)
    jkjke.
    econstructor; eauto.

    (*
    rewrite Heqp.
    simpl.
    econstructor; eauto.
     *)
    jkjke.
    (*
    rewrite Heqp.
    simpl.
    eassumption. *)
    
    eassumption.
    eauto.
  -
    df.
    (*
    cbn in *.

    repeat break_let.
    simpl in *.
    monad_unfold.
    Print dosome. *)
    dosome.
    (*
    df.
    unfold run_vm in *.

    
    repeat break_match;
      try solve_by_inversion.
    repeat find_inversion.
    unfold run_vm in *.
    monad_unfold.
    monad_unfold. *)
    
    (*
    rewrite Heqp3 in *.
    repeat break_let.
    repeat find_inversion.
    simpl in *.
    vmsts.
    repeat find_inversion.
    simpl in *. *)

    allMappedFacts.
    (*

    invc H8. *)
    (*invc H.
    + *)
    vmsts.

    (*
    edestruct suffix_prop.
    rewrite Heqp.
    reflexivity.
    simpl.
    eassumption. *)

    assert (exists l, st_trace2 = st_trace1 ++ l) as HHH.
    {
      eapply suffix_prop.
      rewrite Heqp.
      reflexivity.
      simpl.
      eassumption.
    }
    destruct HHH as [H HH].
    rewrite HH in *.
    clear HH.

    assert (exists l, st_trace0 = (st_trace1 ++ H) ++ l) as HHH.
    {
      eapply suffix_prop.
      rewrite Heqp1.
      reflexivity.
      simpl.
      eassumption.
    }
    destruct HHH as [H' HH].
    rewrite HH in *.
    clear HH.


    
    edestruct app_some'';
      try (rewrite Heqp; eauto);
      try (simpl; eauto).

    (*
      +
      rewrite Heqp.
      reflexivity.
      +
        
      simpl.
      eassumption.
      +
        reflexivity.
      +
        
        reflexivity.
      +
        
        reflexivity.
      +
        
      simpl in *.
      eassumption.
      +
        
      simpl.
      eassumption.
      +
        
        reflexivity.
      +
        
        reflexivity.
      + *)
    
    simpl in *.
    unfold runSt in *.

    edestruct app_some''.
    +
      rewrite Heqp1.
      reflexivity.
    +
      simpl.
      eassumption.
    +
      reflexivity.
    +     
      reflexivity.
    +    
      reflexivity.
    +  
      simpl in *.
      eapply multi_ev_eval.
      ++
        rewrite Heqp.
        reflexivity.
      ++
        simpl.
        eapply restl'.
        rewrite Heqp.
        reflexivity.
        eassumption.
      ++
        eassumption.
      ++
        simpl.
        reflexivity.
    +
      simpl.
      do_pl_immut.
      eassumption.
    +
      reflexivity.
    +
      reflexivity.
    +
      simpl in *.
      unfold runSt in *.
      do_pl_immut.

      measEventFacts.


      invEvents.
      ++
        
        assert (unanno a0 = t'1) as HHHH.
        {
          erewrite <- announ'.
          rewrite Heqp.
          simpl.
          reflexivity.
        }
        rewrite HHHH in H1.
        clear HHHH.

        destruct (x {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hey.
        destruct (x0 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:hey'.
        vmsts.
        rewrite Heqp0 in *.
        simpl in H1.
        invc H1.
        rewrite Heqp2 in *.
        invc hey'.

        destruct (gen_appraisal_comp st_ev2 (eval t'1 st_pl0 et) a_st) eqn:hihihi.
        simpl in *.
        rewrite H0 in *.

        assert (forall ev', In ev' st_trace4 -> In ev' st_trace3).
        {
          intros.
          Check gen_lseq_decomp.
          eapply gen_lseq_decomp.
          reflexivity.
          rewrite Heqp1.
          apply Heqp4.
          rewrite announ'.
          (*
          assert (unanno a1 = t'2).
          {
            erewrite <- announ'.
            rewrite Heqp1.
            simpl.
            reflexivity.
          }
          
          rewrite <- H2. *)
          eassumption.
          assert (o0 = Some tt).
          {
            eapply dodo.
            apply Heqp0.
            apply Heqp2.
          }
          subst.
          
          eassumption.
          eassumption.
          assert (o = Some tt).
          {
            eapply dodo; eauto.
          }
          subst.
          eassumption.
          eassumption.
        }


        (*
        

        assert (exists l, st_trace3 = st_trace4 ++ l).
        {


          assert (unanno a1 = t'2) as GG.
          {
            erewrite <- announ'.
            rewrite Heqp1.
            reflexivity.
          } 
          rewrite <- GG in *.
          clear GG.

          assert (unanno a0 = t'1) as GG.
          {
            erewrite <- announ'.
            rewrite Heqp.
            reflexivity.
          } 
          rewrite <- GG in *.
          clear GG.

          eapply gen_lseq_decomp.
          +
            eassumption.
          + eassumption.
          + eassumption.
          + eassumption.
          + eassumption.
        }

        (*
        
            
            
            
            




          
          +
            apply Heqp3.
          +
            
            apply Heqp4.
          +
            

            eassumption.
          +
            
            
            eassumption.
          +
            
            eassumption.
          +
            
            
            eassumption.
          +
            eassumption.
        } *)
        destruct_conjs.
        rewrite H2.
        clear H2.
         *)
        

        (*
      destruct (gen_appraisal_comp st_ev2 (eval t'1 st_pl0 et) a_st) eqn:hii.
      simpl in *.
      subst. *)
        

        edestruct IHt'1 with (st_trace := st_trace4);
          try (try rewrite Heqp; try econstructor; eauto; tauto).
        (*
        +++
          
          rewrite Heqp.
          eassumption.
        +++
          
          eassumption.
        +++
          
          rewrite Heqp.
          eassumption.
        +++
          
          rewrite Heqp.
          econstructor.
          eassumption.
          eassumption.
        +++
          
          (*
      assert (unanno a0 = t'1) as GG.
        {
          erewrite <- announ'.
          rewrite Heqp.
          reflexivity.
        }
        rewrite GG in *.
        clear GG. *)
          eassumption.
        +++
          
          eassumption. *)
        +++
          
          invc H2.
          exists x1.
          split.
          Search In.
          assert (forall ev', In ev' st_trace4 -> In ev' st_trace3).
          {
            intros.
            eapply gen_lseq_decomp.
            reflexivity.
            rewrite Heqp1.
            apply Heqp4.
            (*
            assert (unanno a1 = t'2).
            {
              erewrite <- announ'.
              rewrite Heqp1.
              simpl.
              reflexivity.
            }
            
            
            rewrite H2. *)
            rewrite announ'.
            eassumption.
            assert (o0 = Some tt).
            {
              eapply dodo.
              apply Heqp0.
              apply Heqp2.
            }
            subst.
            
            eassumption.
            eassumption.
          assert (o = Some tt).
          {
            eapply dodo; eauto.
          }
          subst.
          eassumption.
          eassumption.
          }
          apply H0.
          eassumption.
          eassumption.
          (*
          eapply in_or_app.
          left.
          eauto.
          eassumption. *)
      ++
        
        
        assert (unanno a0 = t'1).
        {
          erewrite <- announ'.
          rewrite Heqp.
          reflexivity.
        }
        rewrite H2 in H1.
        rewrite Heqp0 in *.
        simpl in H1.
        invc H1.

        eapply IHt'2;
          try (try rewrite Heqp1; try econstructor; eauto; tauto).
        

        (*
        +++
          
          rewrite Heqp1.
          eassumption.
        +++ *)
          
        eapply multi_ev_eval.
          
          ++++
            rewrite Heqp.
            reflexivity.
          ++++
            simpl.
            eapply restl'.
            +++++
              rewrite Heqp.
            reflexivity.
            +++++
              eassumption.
          ++++
            eassumption.
          ++++
            simpl.
            reflexivity.

  -


    df.
    vmsts.
    simpl in *.
    dosome.
    vmsts.
    simpl in *.
    do_pl_immut.
    measEventFacts.


    

   

    assert (o = Some tt).
    {
      Check app_some''.
      eapply dodo.
      apply Heqp3.
      eassumption.
      (*
      assert (t'1 = unanno a0).
      admit.
      rewrite H1 in Heqp3.
      apply Heqp3.
      eassumption.
      eassumption. *)
    }

    subst.
    df.

(*
    destruct (v1 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:heyhey.
      vmsts.
      assert (o = Some tt).
      {
        admit.
      }
      subst.
      df. *)

      (*
      assert (o1 = Some tt).
      {
        admit.
      }
      subst. *)


    
    invEvents;
      try solve_by_inversion.



    + (* a0  case *)

      invc H8.
      ++
        cbn in *.

        edestruct IHt'1.
        (*
          [rewrite Heqp; eassumption | econstructor |
           rewrite Heqp; eassumption | rewrite Heqp; econstructor; eassumption | eassumption | eassumption]. *)
        +++
        rewrite Heqp.
        eassumption.
        +++
          econstructor.
        +++
          
        rewrite Heqp.
        eassumption.
        +++
        rewrite Heqp.
        econstructor.
        eassumption.
        eassumption.
        +++
          eassumption.
        +++
            eassumption.
        +++
            

        (*
        edestruct app_some''.
        rewrite Heqp.
        reflexivity.
        simpl.
        eassumption.
        reflexivity.
        reflexivity.
        reflexivity.
        simpl.
        econstructor.
        simpl.
        eassumption.
        reflexivity.
        reflexivity.
        simpl in *.
        unfold runSt in *. *)


          edestruct trace_cumul.
            ++++
              apply Heqp4.
              ++++
                apply Heqp5.
              ++++
        rewrite H1.
        destruct_conjs.
        exists x.
        split.
        eapply in_or_app.
        left.
        eassumption.
        eassumption.
      ++
        
        cbn in *.

        edestruct IHt'1.
        (*
          try (rewrite Heqp; eassumption);
          try (econstructor; tauto);
          try eassumption;
          try (rewrite Heqp; econstructor; eassumption). *)
        +++
        rewrite Heqp.
        eassumption.
        +++
          econstructor.
        +++
          
        rewrite Heqp.
        eassumption.
        +++
          
        rewrite Heqp;
        econstructor;
        eassumption.
       
        +++
          eassumption.
        +++
          
          eassumption.
      +++
        
        destruct_conjs.

        edestruct trace_cumul.
        apply Heqp4.
        apply Heqp5.
        subst.

        exists x.
        split.
        eapply in_or_app.
        left.
        eassumption.
        eassumption.
      ++
        cbn in *.

        edestruct IHt'1.
        +++
        rewrite Heqp.
        eassumption.
        +++
          eassumption.
        +++
          
        rewrite Heqp.
        eassumption.
        +++
        rewrite Heqp.
        econstructor;
          eassumption.
        +++
          eassumption.
        +++
          
          eassumption.
        +++
          
        destruct_conjs.

        edestruct trace_cumul.
        apply Heqp4.
        apply Heqp5.
        subst.

        exists x.
        split.
        eapply in_or_app.
        left.
        eassumption.
        eassumption.
      ++
        cbn in *.

        edestruct IHt'1.
        +++
        rewrite Heqp.
        eassumption.
        +++
          eassumption.
        +++
          
        rewrite Heqp.
        eassumption.
        +++
          
        rewrite Heqp.
        econstructor;
          eassumption.
        +++
        
        
          eassumption.
        +++
          
          eassumption.
        +++
          
        destruct_conjs.

        edestruct trace_cumul.
        apply Heqp4.
        apply Heqp5.
        subst.

        exists x.
        split.
        ++++
        eapply in_or_app.
        left.
        eassumption.
        ++++
        eassumption.
    + (* a1  case *)

      
      destruct (v1 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |}) eqn:heyhey.
      vmsts.
      assert (o = Some tt).
      {
        Check app_some''.
        eapply dodo.
        apply Heqp4.
        eassumption.
      }
      subst.
      df.

      (*
      assert (o1 = Some tt).
      {
        admit.
      }
      subst. *)

      

      invc H8.
      ++
        cbn in *.

        edestruct IHt'2.
        +++
        rewrite Heqp1.
        eassumption.
        +++
          econstructor.
        +++
          
        rewrite Heqp1.
        eassumption.
        +++
        rewrite Heqp1.
        econstructor;
          eassumption.
        +++
        gen_st_const.
        eassumption.
        +++
          eassumption.
        +++
          

        edestruct trace_cumul.
        apply Heqp4.
        apply Heqp5.
        subst.
        destruct_conjs.
        exists x.
        split.
        ++++
        assert (x0 = st_trace0).
        {
          assert (o1 = Some tt).
          {
            eapply dodo.
            apply Heqp4.
            eassumption.
          }

          subst.



          eapply gogo; eauto.
        }

        subst.
        eapply in_or_app.
        right.
        eassumption.
        ++++
        eassumption.
      ++

        cbn in *.

        edestruct IHt'2.
        rewrite Heqp1.
        eassumption.
        eassumption.
        rewrite Heqp1.
        eassumption.
        rewrite Heqp1.
        econstructor.
        eassumption.
        eassumption.
        gen_st_const.
        eassumption.
        eassumption.

        edestruct trace_cumul.
        apply Heqp4.
        apply Heqp5.
        subst.
        destruct_conjs.
        exists x.
        split.
        assert (x0 = st_trace0).
        {

          assert (o1 = Some tt).
          {
            eapply dodo.
            apply Heqp4.
            eassumption.
          }

          subst.



          eapply gogo; eauto.

        }
        subst.
        eapply in_or_app.
        right.
        eassumption.
        eassumption.
      ++
        cbn in *.

        edestruct IHt'2.
        rewrite Heqp1.
        eassumption.
        econstructor.
        rewrite Heqp1.
        eassumption.
        rewrite Heqp1.
        econstructor.
        eassumption.
        eassumption.
        gen_st_const.
        eassumption.
        eassumption.

        edestruct trace_cumul.
        apply Heqp4.
        apply Heqp5.
        subst.
        destruct_conjs.
        exists x.
        split.
        assert (x0 = st_trace0).
        {
          assert (o1 = Some tt).
          {
            eapply dodo.
            apply Heqp4.
            eassumption.
          }

          subst.



          eapply gogo; eauto.
        }
        subst.
        eapply in_or_app.
        right.
        eassumption.
        eassumption.
      ++
        cbn in *.

        edestruct IHt'2.
        rewrite Heqp1.
        eassumption.
        eassumption.
        rewrite Heqp1.
        eassumption.
        rewrite Heqp1.
        econstructor.
        eassumption.
        eassumption.
        gen_st_const.
        eassumption.
        eassumption.

        edestruct trace_cumul.
        apply Heqp4.
        apply Heqp5.
        subst.
        destruct_conjs.
        exists x.
        split.
        assert (x0 = st_trace0).
        {
          assert (o1 = Some tt).
          {
            eapply dodo.
            apply Heqp4.
            eassumption.
          }

          subst.



          eapply gogo; eauto.
        }
        subst.
        eapply in_or_app.
        right.
        eassumption.
        eassumption.
  -

    reflexivity; tauto; tauto.
    
        









        
        
        

        (*
        edestruct app_some''.
        rewrite Heqp.
        reflexivity.
        simpl.
        eassumption.
        reflexivity.
        reflexivity.
        reflexivity.
        simpl.
        econstructor.
        simpl.
        eassumption.
        reflexivity.
        reflexivity.
        simpl in *.
        unfold runSt in *. *)

       
        edestruct trace_cumul.
        apply Heqp4.
        eassumption.
        rewrite H1.
        destruct_conjs.
        exists x.
        split.
        eapply in_or_app.
        left.
        destruct_conjs.
        eassumption.
        eassumption.

      
      
      
        
        
        
        
        


        
        do_pl_immut.
        eassumption.
        
      
      
    
      
      

      
      
      

      
      destruct (gen_appraisal_comp st_ev2 (eval t'1 st_pl0 et) a_st) eqn:hi.
      eapply IHt'1.
      rewrite Heqp.
      eassumption.
      eassumption.
      rewrite Heqp.
      eassumption.
      rewrite Heqp.
      econstructor.
      eassumption.
      eassumption.

      simpl in *.
      subst.
      eassumption.
      simpl in *.
      subst.
      reflexivity.
      rewrite hi in *.


      eapply IHt'2.
      rewrite Heqp1.
      eassumption.
      eapply multi_ev_eval.
      rewrite Heqp. reflexivity.
      simpl.
      eapply restl'.
      rewrite Heqp. reflexivity.
      eassumption.
      eassumption.
      simpl.
      reflexivity.
      rewrite Heqp1.
      eassumption.
      rewrite Heqp1.
      
      
      
      
      


      
      
      simpl.
      eassumption.
      reflexivity.
      reflexivity.
      simpl in *.
      unfold runSt in *.

      
     
     
      eapply multi_ev_eval.
      ++
      rewrite Heqp.
      reflexivity.
      ++
        
      
      simpl.
      eapply restl'.
      rewrite Heqp.
      simpl. reflexivity.

      eapply Heqp3.
      ++
        
        eassumption.
      ++
        
        reflexivity.
      
        
      
    +
      jkjke.
      simpl.
      do_pl_immut.
      eassumption.
      
     
    +

      simpl in *.

      eapply IHt'2.
      rewrite Heqp1.
      eassumption.
      eapply multi_ev_eval;
        try reflexivity.
      ++
        rewrite Heqp.
        simpl.
        eapply restl'.
        rewrite Heqp.
        reflexivity.
        eassumption.
      ++
        eassumption.
      ++
        rewrite Heqp1.
        rewrite announ' in *.
        do_pl_immut.
        assert (t'1 = unanno a0).
        {
          erewrite <- announ'.
            rewrite Heqp1.
            simpl.
            reflexivity.
          admit.
        }
        subst.
        eassumption.
      ++

        invc H9.
        do_pl_immut.
        invc H1.

        econstructor.
        
        
        
        
        
        
        reflexivity.
        
     
      

      (*
      rewrite Heqp0.
      simpl.
      dunit.
      apply Heqp3.
      eassumption. *)
      reflexivity.
      reflexivity.
      reflexivity.

      reflexivity; tauto; tauto.

      
      rewrite Heqp0.
      simpl.
      invc H6.
      eassumption.
      reflexivity.
      reflexivity.
      unfold runSt in *.

      edestruct app_some'' with (t:=a1).
      rewrite Heqp2.
      reflexivity.
      eassumption.
      eapply multi_ev_eval.
      reflexivity.
      rewrite Heqp0.
      simpl.
      admit.
      eassumption.
      rewrite Heqp0.
      simpl.
      reflexivity.
      invc H6.
      assert (p = st_pl).
      {
        admit.
      }
      subst.
      eassumption.
      reflexivity.
      reflexivity.
      unfold runSt in *.

      eapply IHt'2.
      reflexivity.
      eapply multi_ev_eval.
      reflexivity.
      rewrite Heqp0.
      simpl.
      admit.
      eassumption.
      rewrite Heqp0.
      simpl.
      reflexivity.
      rewrite Heqp2.
      simpl.
      eassumption.
      reflexivity; tauto.









      
      
      
      eapply IHt'1.
      reflexivity.
      eassumption.
      rewrite Heqp0.
      simpl.
      dunit.
      eassumption.
      rewrite Heqp0.
      simpl.
      econstructor.
      eassumption.
      eassumption.
      rewrite Heqp0.
      simpl.
      invc H6.
      eassumption.
      rewrite Heqp0.
      simpl.
      rewrite Heqp3.
      simpl.
      Check app_some''.

     
      
      
      

      invc H6.
      invc H0.
       *)
      
      eapply IHt'2.
      reflexivity.
      eapply multi_ev_eval.
      reflexivity.
      rewrite Heqp0.
      simpl.
      admit.
      
      
      eassumption.
      rewrite announ'.
      reflexivity.
      rewrite Heqp2.
      simpl.
      eassumption.
      rewrite Heqp2.
      simpl.
      econstructor.


      
      eassumption.

      edestruct IHt'1 with (ev:= (umeas n1 p0 i args)).
      reflexivity.
      eassumption.
      rewrite Heqp0.
      simpl.
      dunit.
      apply Heqp3.
      rewrite Heqp0.
      simpl.
      econstructor.
      eassumption.
      econstructor.
      rewrite Heqp0.
      simpl.
      eassumption.
      rewrite Heqp0.
      simpl.
      rewrite Heqp3.
      simpl.
      invc H8.
      econstructor
      
    
    
      
      
      
      
      
        
      destruct v0.
      repeat find_inversion.
      
      eexists.
      split.
      left.
      reflexivity.
      invc H10.
      inv H.
      simpl.
      econstructor.
      reflexivity.
      econstructor.
      simpl in *.
      eassumption.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    
    


Lemma app_correct :
  forall t t' p' app_comp app_comp_res app_comp_st tr_app_comp ev a_st st',

    t = snd (anno t' p') ->
    build_comp t empty_vmst = (Some tt, st') ->
    app_comp = exec_app_comp_t t' 0 p' empty_vmst  (* AM vm_st *) ->
    app_comp_res = runSt a_st app_comp (* ((option vm_st) * AM_St) *)  -> 
    app_comp_st = fromOpt (fst app_comp_res) empty_vmst (* vm_st *)  ->
    tr_app_comp = st_trace app_comp_st ->
    allMapped t 0 a_st mt ->                    
    measEvent t 0 ev ->

    exists ev', In ev' tr_app_comp /\ appEvent ev a_st ev'.
Proof.
  intros.
  edestruct app_some.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  subst.
  unfold runSt in *.
  unfold exec_app_comp_t in *.
  unfold exec_app_comp in *.
  monad_unfold.
  unfold build_app_comp in *.
  monad_unfold.
  repeat break_match; try solve_by_inversion.
  repeat find_inversion.
  rewrite announ' in *.
  simpl in *.
  assert (snd (runSt empty_vmst v) = x).
  congruence.
  clear H7.
  rewrite H.
  generalize dependent p'.
  generalize dependent ev.
  generalize dependent a_st.
  generalize dependent st'.
  generalize dependent x.
  generalize dependent a.
  generalize dependent v.

  induction t'; intros.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    destruct a;
      monad_unfold;
      repeat find_inversion;
      monad_unfold;
      repeat find_inversion.
    +
      
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    +
      cbn in *.
      repeat break_let.
      repeat find_inversion.
      destruct o;
        try solve_by_inversion.
      repeat find_inversion.
      inv H6.
      inv H0.
      inv H5.
      destruct_conjs.
      invc H1.
      rewrite H2 in *.
      monad_unfold.
      repeat find_inversion.
      eexists.
      split.
      left.
      reflexivity.
      invc H10.
      inv H.
      simpl.
      econstructor.
      reflexivity.
      econstructor.
      simpl in *.
      eassumption.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
    +
      cbn in *.
      inv H6.
      inv H0.
      inv H.
  -
    cbn in *.
    repeat break_let.
    simpl in *.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    repeat find_inversion.
    inv H6.
    cbn in *.
    unfold run_vm in *.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    repeat find_inversion.
    simpl in *.
    inv H0.
    inv H.
    inv H5.
    eapply IHt'.
    reflexivity.
    rewrite Heqp.
    simpl.
    Print build_comp_at.
    apply build_comp_at.
    invc H6.
    clear H2.
    clear H1.
    econstructor.
    rewrite Heqp.
    simpl.
    admit.
    econstructor.
    rewrite Heqp.
    simpl.


    
    edestruct IHt'.
    reflexivity.
    cbn in *.
    
    
      
      
      
      
      destruct a0.
      econstructor.
      
      
    
  
      
    
    
  

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
  
  
  
















(***** Extra proof stuffs *******)


(*
(* Not true bc of bseq (NONE,NONE) case *)
Lemma asas : forall e' a2 p' et a_st' x0,
    gen_appraisal_comp e' (eval (unanno a2) p' et) a_st' = (Some x0, a_st') ->
    evMapped et a_st'.
Proof.
  intros.
  Check evshape_et.
  Check gen_ev_mapped.
  eapply gen_ev_mapped.
Abort.
*)

(*
Lemma measEventAt : forall t n p ev,
    measEvent (annotated (att n t)) p ev ->
    measEvent (annotated t) n ev.
Proof.
  intros.
  unfold annotated in *.
  Check measEventAt'.
  eapply measEventAt'.
  split
  unfold annotated in *.
  eapply measEventAt'.
  eapply measEventAt'; eauto.
Defined.
 *)


(*
Lemma app_correct' :
  forall t t' p' app_comp app_comp_res app_comp_st tr_app_comp ev a_st vm_st' e tr p o et,

    t = snd (anno t' p') ->
    build_comp t {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} = (Some tt, vm_st') ->
    app_comp = exec_app_comp_t t' p' {| st_ev:=e; st_trace:=tr; st_pl:=p; st_store:=o|} et  (* AM vm_st *) ->
    Ev_Shape e et ->
    app_comp_res = runSt a_st app_comp (* ((option vm_st) * AM_St) *)  -> 
    app_comp_st = fromOpt (fst app_comp_res) empty_vmst (* vm_st *)  ->
    tr_app_comp = st_trace app_comp_st ->
    allMapped t p a_st et ->                    
    measEvent t p ev ->

    exists ev', In ev' tr_app_comp /\ appEvent ev a_st ev'.
 *)


    

(*
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
 *)



(*
Lemma eval_evshape : forall t' p',
      Ev_Shape
      (st_ev
       (snd
          (build_comp (snd (anno t' p'))
                      {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |})))
      (eval t' 0 mt).
Proof.
Admitted.
*)

(*
    Lemma build_at : forall r n t st st',
      build_comp (aatt r n t) st = (Some tt,st') ->
      build_comp t st = (Some tt, st').
    Proof.
    Admitted.
*)






(**** Long asdd proof attempts *)

(*
Lemma asdd : forall a e' p et a_st a_st' x0 p' t' ,
    a = snd (anno t' p') ->
    gen_appraisal_comp e' (eval (unanno a) p et) a_st = (Some x0, a_st') ->
    allMapped a p a_st et.
Proof.
  induction a; destruct et;
    intros;
    try ( cbn in *; (* att cases *)
          destruct t';
          try (cbn in *;
               repeat break_let;
               cbn in *;
               try solve_by_inversion;
               invc H);  
          econstructor;
          [reflexivity | 
           eapply IHa; [rewrite Heqp0; cbn in *; eauto | eauto]]).
  -
    destruct a;
      try (
          df;
          destruct e';
          stt;
          df;
          econstructor;
          econstructor; tauto);
      try (
          df;
          destruct e';
          stt;
          df;
          econstructor;
          [econstructor | reflexivity | eexists; econstructor; eauto];
          tauto).

  -
    destruct a;
      try (
    
      df;
      destruct e';
      stt;
      econstructor;
      econstructor;
      [reflexivity | eapply gen_ev_mapped; eauto | eexists; econstructor; eauto];
      tauto);
      try (
          df;
      destruct e';
        stt;
      destruct e';
      stt;
      try (
        econstructor;
        [reflexivity | eapply gen_ev_mapped; eauto | eexists; econstructor; eauto]));
      try (
          econstructor; 
          [econstructor; [reflexivity | eapply gen_ev_mapped; eauto | eexists; econstructor; eauto] | reflexivity |
         eexists; econstructor; eauto];
          tauto).
      

    +
      df.
      econstructor.
      econstructor.
      reflexivity.
      eapply gen_ev_mapped.
      eauto.
      eexists.
      econstructor.
      eauto.

  -
        destruct a;
      try (
    
      df;
      destruct e';
      stt;
      econstructor;
      econstructor;
      [reflexivity | eapply gen_ev_mapped; eauto | eexists; econstructor; eauto];
      tauto);
      try (
          df;
      destruct e';
        stt;
      destruct e';
      stt;
      try (
        econstructor;
        [reflexivity | eapply gen_ev_mapped; eauto | eexists; econstructor; eauto]));
      try (
          econstructor; 
          [econstructor; [reflexivity | eapply gen_ev_mapped; eauto | eexists; econstructor; eauto] | reflexivity |
         eexists; econstructor; eauto];
          tauto).
      

    +
      df.
      econstructor.
      econstructor.
      reflexivity.
      eapply gen_ev_mapped.
      eauto.
      eexists.
      econstructor.
      eauto.
  -

    destruct a.
    +
      df.
      destruct e';
        stt.
      econstructor.
      econstructor.
      eapply gen_ev_mapped; eauto.
    +
      df.
      destruct e';
        stt.
      destruct e'; stt.
      econstructor.
      econstructor.
      eapply gen_ev_mapped; eauto.
      reflexivity.
      eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      destruct e'; stt.
      econstructor.
      econstructor.
      eapply gen_ev_mapped; eauto.
      reflexivity.
      eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      destruct e'; stt.
      econstructor.
      econstructor.
      eapply gen_ev_mapped; eauto.
  -
        destruct a.
    +
      df.
      destruct e';
        stt.
      econstructor.
      econstructor.
      reflexivity.
      eapply gen_ev_mapped; eauto.
    +
      df.
      destruct e';
        stt.
      destruct e'; stt.
      econstructor.
      econstructor.
      reflexivity.
      eapply gen_ev_mapped; eauto.
      reflexivity.
      eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      destruct e'; stt.
      econstructor.
      econstructor.
      reflexivity.
      eapply gen_ev_mapped; eauto.
      reflexivity.
      eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      destruct e'; stt.
      econstructor.
      econstructor.
      reflexivity.
      eapply gen_ev_mapped; eauto.
  -

    destruct a.
    +
      df.
      destruct e';
        stt.
      gen_st_const.
      econstructor.
      econstructor.
      
      
      eapply gen_ev_mapped; eauto.
      eapply gen_ev_mapped; eauto.
    +
      df.
      destruct e';
        stt.
      gen_st_const.
       destruct e';
         stt.
       gen_st_const.
       econstructor.
       econstructor.
         eapply gen_ev_mapped; eauto.
         eapply gen_ev_mapped; eauto.
         reflexivity.
         eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      gen_st_const.
       destruct e';
         stt.
       gen_st_const.
       econstructor.
       econstructor.
         eapply gen_ev_mapped; eauto.
         eapply gen_ev_mapped; eauto.
         reflexivity.
         eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      gen_st_const.
       destruct e';
         stt.
       gen_st_const.
       econstructor.
       econstructor.
         eapply gen_ev_mapped; eauto.
         eapply gen_ev_mapped; eauto.
         
  -
        destruct a.
    +
      df.
      destruct e';
        stt.
      gen_st_const.
      econstructor.
      econstructor.
      
      
      eapply gen_ev_mapped; eauto.
      eapply gen_ev_mapped; eauto.
    +
      df.
      destruct e';
        stt.
      gen_st_const.
       destruct e';
         stt.
       gen_st_const.
       econstructor.
       econstructor.
         eapply gen_ev_mapped; eauto.
         eapply gen_ev_mapped; eauto.
         reflexivity.
         eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      gen_st_const.
       destruct e';
         stt.
       gen_st_const.
       econstructor.
       econstructor.
         eapply gen_ev_mapped; eauto.
         eapply gen_ev_mapped; eauto.
         reflexivity.
         eexists; econstructor; eauto.
    +
        df.
      destruct e';
        stt.
      gen_st_const.
       destruct e';
         stt.
       gen_st_const.
       econstructor.
       econstructor.
         eapply gen_ev_mapped; eauto.
         eapply gen_ev_mapped; eauto.





    
  -

    Print annogo.

    Ltac dot' t H :=
       destruct t;
          try (cbn in *;
               repeat break_let;
               cbn in *;
               try solve_by_inversion;
               invc H).

    
    cbn in *.
    dot' t' H.
    
    assert (exists t' p', a0 = snd (anno t' p')).
    {
      repeat eexists.
      rewrite Heqp1.
      eauto.
    }
    destruct_conjs.
    
    destruct (build_comp a0 {| st_ev := mtc; st_trace := []; st_pl := p; st_store := [] |}) eqn:hoho.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a0) p mt) a_st) eqn:hohoho.
    Print gen_st_const.
    Ltac gen_st_const' :=
      let tac := eapply gen_const; eauto in
      repeat match goal with
             | H:gen_appraisal_comp ?e ?et ?A = (?o, ?B) |- _ => assert_new_proof_by (A = B) tac
             end.
    
    gen_st_const'.
    rewrite H4 in *.
    rewrite H3 in *.
    clear H3; clear H4.
    Check evshape_et.
    edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a0) p mt)).
    eapply multi_ev_eval.
    eassumption.

    assert (o = Some tt).
    {
      eapply always_some.
      reflexivity.
      rewrite <- H2.
      eassumption.
    }
    rewrite H3 in *. clear H3.
    eassumption.
    econstructor.
    reflexivity.
Admitted.
*)



    (*
      eapply asas. eassumption.
      rewrite H3 in *.
      df.
    
    


    (*
    assert (exists hh, o0 = Some hh).
    {
      Lemma gen_some''' : forall e et a_st a_st' o,
        gen_appraisal_comp e et a_st = (o,a_st') ->
        evMapped et a_st ->
        (exists hh, o = Some hh).
      Proof.
      Admitted.

      Check evshape_et.
      Check gen_ev_mapped.



      eapply gen_some'''.
      eassumption.

      eapply asas.
      eassumption.
      
    }
    
    destruct_conjs.
    subst. *)
    
    econstructor.
    eapply IHa1.
    eassumption.
    
    eapply IHa2; eauto.
  -

    cbn in *.
    assert (exists t' p', a1 = snd (anno t' p')).
    {
      admit.
    }
    destruct_conjs.

    assert (exists e vm_st',
               build_comp a1 {| st_ev := e; st_trace := []; st_pl := p'; st_store := [] |} =
               (Some tt, vm_st')).
    admit.
    destruct_conjs.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a1) p'  (uu n l n0 et)) a_st) eqn:hohoho.
    Print gen_st_const.
   
    
    gen_st_const'.
    rewrite H4 in *.
    rewrite H6 in *.
    clear H6; clear H4.
    Check evshape_et.
    edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1) p'  (uu n l n0 et))).
    eapply multi_ev_eval.
    eassumption.
    eassumption.

    (*

    assert (o = Some tt).
    {
      eapply always_some.
      reflexivity.
      rewrite <- H2.
      eassumption.
    }
    rewrite H3 in *. clear H3. *)

    assert (Ev_Shape H3 (uu n l n0 et)).
    admit.
    eassumption.
    reflexivity.
   


      
      eapply asas. eassumption.
      rewrite H4 in *.
      df.
    
    


    (*
    assert (exists hh, o0 = Some hh).
    {
      Lemma gen_some''' : forall e et a_st a_st' o,
        gen_appraisal_comp e et a_st = (o,a_st') ->
        evMapped et a_st ->
        (exists hh, o = Some hh).
      Proof.
      Admitted.

      Check evshape_et.
      Check gen_ev_mapped.



      eapply gen_some'''.
      eassumption.

      eapply asas.
      eassumption.
      
    }
    
    destruct_conjs.
    subst. *)
    
    econstructor.
    eapply IHa1.
    eassumption.
    
    eapply IHa2; eauto.











    











(*
    
    cbn in *.
    assert (exists t' p', a1 = snd (anno t' p')).
    {
      admit.
    }
    destruct_conjs.
    destruct (build_comp a1 {| st_ev := mtc; st_trace := []; st_pl := p'; st_store := [] |}) eqn:hoho.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a1) p' (uu n l n0 mt)) a_st) eqn:hohoho.
    gen_st_const'.
    rewrite H4 in *.
    rewrite H3 in *.
    clear H4; clear H3.

        assert (o = Some tt).
    {
      eapply always_some.
      reflexivity.
      rewrite <- H2.
      eassumption.
    }
    rewrite H3 in *. clear H3.


    edestruct evshape_et with (e:=st_ev) (et:=(eval (unanno a1) p' mt)).
    eapply multi_ev_eval.
    eassumption.
    eassumption.
    econstructor.
    reflexivity.
    

    eapply asas.
    eassumption.
    rewrite H3 in *.
    eassumption.
    


    
    


    
    assert (exists hh, o0 = Some hh).
    {
      admit.
    }
    
    destruct_conjs.
    subst.

    econstructor.
    eapply IHa1.
    eapply hohoho.
    eapply IHa2; eauto. *)
  -
    cbn in *.
    destruct (build_comp a1 empty_vmst) eqn:hoho.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a1) p' (gg n et)) a_st) eqn:hohoho.
    gen_st_const.
    assert (exists hh, o0 = Some hh).
    {
      admit.
    }
    
    destruct_conjs.
    subst.

    econstructor.
    eapply IHa1.
    eapply hohoho.
    eapply IHa2; eauto.
  -
    cbn in *.
    destruct (build_comp a1 empty_vmst) eqn:hoho.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a1) p' (hh n et)) a_st) eqn:hohoho.
    gen_st_const.
    assert (exists hh, o0 = Some hh).
    {
      admit.
    }
    
    destruct_conjs.
    subst.

    econstructor.
    eapply IHa1.
    eapply hohoho.
    eapply IHa2; eauto.
  -
    cbn in *.
    destruct (build_comp a1 empty_vmst) eqn:hoho.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a1) p' (nn n et)) a_st) eqn:hohoho.
    gen_st_const.
    assert (exists hh, o0 = Some hh).
    {
      admit.
    }
    
    destruct_conjs.
    subst.

    econstructor.
    eapply IHa1.
    eapply hohoho.
    eapply IHa2; eauto.
  -
    cbn in *.
    destruct (build_comp a1 empty_vmst) eqn:hoho.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a1) p' (ss et1 et2)) a_st) eqn:hohoho.
    gen_st_const.
    assert (exists hh, o0 = Some hh).
    {
      admit.
    }
    
    destruct_conjs.
    subst.

    econstructor.
    eapply IHa1.
    eapply hohoho.
    eapply IHa2; eauto.
  -
        cbn in *.
    destruct (build_comp a1 empty_vmst) eqn:hoho.
    vmsts.
    unfold empty_vmst in *.

    destruct ( gen_appraisal_comp st_ev (eval (unanno a1) p' (pp et1 et2)) a_st) eqn:hohoho.
    gen_st_const.
    assert (exists hh, o0 = Some hh).
    {
      admit.
    }
    
    destruct_conjs.
    subst.

    econstructor.
    eapply IHa1.
    eapply hohoho.
    eapply IHa2; eauto.
  -
    cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).
  -
        cbn in *.
    destruct e'; stt.
    destruct s0;
      destruct s1;
      cbn in *;
      try (
    
          gen_st_const;
     
          econstructor;
          eauto).

Admitted. 
*)  

(*
Lemma asddd : forall a1 a2 e' p' et a_st x0 a,
    gen_appraisal_comp e' (eval (unanno a2) p' (eval (unanno a1) p' et)) a_st = (Some x0, a) ->
    allMapped a1 p' a_st et.
Proof.
  intros.
  Check asdd.
  assert (allMapped a2 p' a_st (eval (unanno a1) p' et)).
  eapply asdd; eauto.
  assert (evMapped (eval (unanno a1) p' et) a_st).

  Check gen_ev_mapped.
  Check asas.
  eapply asas.
  gen_st_const.
  eauto.
  Lemma ev_imp_all : forall a p et a_st,
    evMapped (eval (unanno a) p et) a_st ->
    allMapped a p a_st et.
  Proof.
  Admitted.
  eapply ev_imp_all; eauto.
Defined.
*)

      
    
(*

Lemma asdd : forall a1 a2 e' p' et a_st x0 a,
    gen_appraisal_comp e' (eval (unanno a2) p' (eval (unanno a1) p' et)) a_st = (Some x0, a) ->
    allMapped a1 p' a_st et.
Proof.
  induction a1; destruct a2; intros.
  -
    destruct a; destruct a0; 
      cbn in *;
      try (econstructor; eapply gen_ev_mapped; eauto; tauto);
    try (destruct e';
         stt;
         econstructor;
         eapply gen_ev_mapped; eauto ;tauto);
    try (destruct e';
         stt;
         try (destruct e'; stt);
         econstructor;
         [eapply gen_ev_mapped; eauto; tauto | reflexivity | eexists; econstructor; eauto];
         tauto);
    try (destruct e';
         stt;
         econstructor;
         [eapply gen_ev_mapped; eauto; tauto | reflexivity | eexists; econstructor; eauto];
         tauto);
    try (
        destruct e';
        stt;
        destruct e';
        stt;
        econstructor;
        eapply gen_ev_mapped; eauto;
        tauto).
  -
    destruct a; destruct a2.
    +
      cbn in *.
      destruct a;
        try (
            destruct e';
            stt;
            econstructor;
            eapply gen_ev_mapped; eauto;
            tauto).
      ++
        destruct e';
          stt.
        break_match; try solve_by_inversion.
        df.
        econstructor.
        econstructor.
        stt.
        break_match; try solve_by_inversion.
        repeat break_let.
        dosome.
        stt.
        econstructor.
        econstructor.
        reflexivity.
        eapply gen_ev_mapped; eauto.
        eexists.
        econstructor.
        eauto.
        repeat break_let.
        repeat break_match; try solve_by_inversion.
        df.
        stt.
        econstructor.
        econstructor.
        reflexivity.
        eapply gen_ev_mapped; eauto.
        eexists.
        econstructor.
        eauto.
        df.


        ff.
        econstructor.
        econstructor.
        eapply gen_ev_mapped; eauto.
        ff.
        econstructor.
        econstructor.
        reflexivity.
        eapply gen_ev_mapped; eauto.
        ff.
        econstructor.
        econstructor.
        eapply gen_ev_mapped; eauto.
        gen_st_const.
        eapply gen_ev_mapped; eauto.
        ff.
        econstructor.
        econstructor.
        eapply gen_ev_mapped; eauto.
        gen_st_const.
        eapply gen_ev_mapped; eauto.
    +
      cbn in *.
       destruct a2;
        try (
            destruct e';
            stt;
            econstructor;
            eapply gen_ev_mapped; eauto;
            tauto).
       admit.
       cbn in *.
       econstructor.
       eapply gen_ev_mapped.
       admit.

       ++

         cbn in *.
          destruct a2;
        try (
            destruct e';
            stt;
            econstructor;
            eapply gen_ev_mapped; eauto;
            tauto).
         



      
      
      ++

        destruct e';
          stt.
        econstructor.
        eapply gen_ev_mapped; eauto.
      ++
        destruct e';
          stt.
        econstructor.
        eapply gen_ev_mapped; eauto.
      ++
        
        
                
        break_match; try solve_by_inversion.
        df.
        econstructor.
        econstructor.
        stt.
        break_match; try solve_by_inversion.
        repeat break_let.
        dosome.
        stt.
        econstructor.
        econstructor.
        reflexivity.
        eapply gen_ev_mapped; eauto.
        eexists.
        econstructor.
        eauto.
        repeat break_let.
        repeat break_match; try solve_by_inversion.
        df.
        stt.
        econstructor.
        econstructor.
        reflexivity.
        eapply gen_ev_mapped; eauto.
        eexists.
        econstructor.
        eauto.
        df.

        Ltac ff := repeat break_match; try solve_by_inversion; df.
        ff.
        econstructor.
        econstructor.
        eapply gen_ev_mapped; eauto.
        ff.
        econstructor.
        econstructor.
        reflexivity.
        eapply gen_ev_mapped; eauto.
        ff.
        econstructor.
        econstructor.
        eapply gen_ev_mapped; eauto.
        gen_st_const.
        eapply gen_ev_mapped; eauto.
        ff.
        econstructor.
        econstructor.
        eapply gen_ev_mapped; eauto.
        gen_st_const.
        eapply gen_ev_mapped; eauto.






        
        
      
        df.
      
      cbn in *;
      try (econstructor; eapply gen_ev_mapped; eauto; tauto);
    try (destruct e';
         stt;
         econstructor;
         eapply gen_ev_mapped; eauto ;tauto);
    try (destruct e';
         stt;
         try (destruct e'; stt);
         econstructor;
         [eapply gen_ev_mapped; eauto; tauto | reflexivity | eexists; econstructor; eauto];
         tauto);
    try (destruct e';
         stt;
         econstructor;
         [eapply gen_ev_mapped; eauto; tauto | reflexivity | eexists; econstructor; eauto];
         tauto);
    try (
        destruct e';
        stt;
        destruct e';
        stt;
        econstructor;
        eapply gen_ev_mapped; eauto;
        tauto).
    
         
      

    +
      destruct e';
        stt.
      destruct e';
        stt.
      econstructor.
      eapply gen_ev_mapped; eauto
      

      


    (*
    +
      destruct e';
        stt.
      econstructor.
      eapply gen_ev_mapped; eauto.
    +
      destruct e';
        stt.
      econstructor.
      eapply gen_ev_mapped; eauto.
      

      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      ++
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        econstructor.
        eapply gen_ev_mapped; eauto.
        (*
        repeat break_let.
        destruct (map_get (st_sigmap a_st) p');
          try solve_by_inversion.
        df.
        eassumption. *)
    +
     

      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      ++
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
         econstructor.
        eapply gen_ev_mapped; eauto.
    (*
                destruct (map_get (st_aspmap a_st) (p', n));
                  try solve_by_inversion.
                df.
                eassumption. *)
     *)




    (*
    +
     

      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      ++
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*
        destruct (map_get (st_aspmap a_st) (p', n));
          try solve_by_inversion.
        df. *)
        econstructor.
      +++
        
        eapply gen_ev_mapped; eauto.
      +++
        reflexivity.
      +++
        eexists.
        econstructor.
        eauto.
        (*
        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*
        destruct (map_get (st_aspmap a_st) (p', n)) eqn:hi.
        df. *)
        
        eexists.
        econstructor.
        eauto. *)
     *)
    (*
    +
     
      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      ++
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.

        try haaa.
        (*
        destruct (map_get (st_aspmap a_st) (p', n0));
          try solve_by_inversion.
        df. *)
        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        econstructor.
        +++
        (*
        destruct (map_get (st_aspmap a) (p', n)) eqn:hey;
          try solve_by_inversion.
        df. *)
        eapply gen_ev_mapped; eauto.
      +++
        reflexivity.
      +++
        eexists.
        econstructor.
        eauto.

        (*
        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*
        destruct (map_get (st_aspmap a_st) (p', n0)) eqn:hi;
          try solve_by_inversion.
        df. *)

        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).

        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*

        destruct (map_get (st_aspmap a) (p', n)) eqn:ho;
          try solve_by_inversion.
         *)
        
        eexists.
        econstructor.
        eauto. *)
     *)
    (*
    +
     
      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      ++
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*
        destruct (map_get (st_sigmap a_st) p');
          try solve_by_inversion.
        df. *)
        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*
        destruct (map_get (st_aspmap a) (p', n)) eqn:hey;
          try solve_by_inversion.
        df. *)
        econstructor.
        +++
        eapply gen_ev_mapped; eauto.
      +++
        reflexivity.
      +++
        (*
        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*
        destruct (map_get (st_sigmap a_st) p') eqn:hi;
          try solve_by_inversion.
        df. *)

        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).

        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa. *)
        (*

        destruct (map_get (st_aspmap a) (p', n)) eqn:ho;
          try solve_by_inversion.
         *)
        
        eexists.
        econstructor.
        eauto.
     *)

    (*
    +
     
      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      ++
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.

        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa.
        (*
        destruct (map_get (st_aspmap a_st) (p', n));
          try solve_by_inversion.
        df. *)
        econstructor.
        +++
        eapply gen_ev_mapped; eauto.
      +++
        reflexivity.
      +++
        (*
        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.

        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        try haaa. *)
        (*
        destruct (map_get (st_aspmap a_st) (p', n)) eqn:hey;
          try solve_by_inversion.
        df. *)
        eexists.
        econstructor.
        eauto.
     *)

    (*
    +
      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      try haaa.
      (*
      destruct ( map_get (st_sigmap a_st) p') eqn:hi;
        try solve_by_inversion. *)
      
      
      econstructor.
      ++
      
        eapply gen_ev_mapped; eauto.
      ++
        
        reflexivity.
      ++
        
      eexists.
      econstructor.
      eassumption.
     *)

    (*
    +
            destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      try haaa.
      (*
      destruct ( map_get (st_sigmap a_st) p') eqn:hi;
        try solve_by_inversion. *)

       destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
       cbn in *.
       monad_unfold.
       repeat break_let.
       dosome.
       try haaa.
      
      econstructor.
      ++
      
        eapply gen_ev_mapped; eauto.
      ++
        
        reflexivity.
      ++
        
      eexists.
      econstructor.
      eassumption.
     *)
    (*
    +
                  destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      try haaa.
      (*
      destruct ( map_get (st_sigmap a_st) p') eqn:hi;
        try solve_by_inversion. *)

       destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
       cbn in *.
       monad_unfold.
       repeat break_let.
       dosome.
       try haaa.
      
      econstructor.
      ++
      
        eapply gen_ev_mapped; eauto.
      ++
        
        reflexivity.
      ++
        
      eexists.
      econstructor.
      eassumption.
     *)
    (*
    +
                  destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      try haaa.
      (*
      destruct ( map_get (st_sigmap a_st) p') eqn:hi;
        try solve_by_inversion. *)

       destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
       cbn in *.
       monad_unfold.
       repeat break_let.
       dosome.
       try haaa.
      
      econstructor.
      ++
      
        eapply gen_ev_mapped; eauto.
      ++
        
        reflexivity.
      ++
        
      eexists.
      econstructor.
      eassumption.
     *)
    
    +
      destruct e';
        stt.
      econstructor.
      eapply gen_ev_mapped; eauto.
      reflexivity.
      eexists.
      econstructor.
      eauto.
    +
      
      


      
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.


      econstructor.
      eapply gen_ev_mapped; eauto.
    +
                        destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      try haaa.
      (*
      destruct ( map_get (st_sigmap a_st) p') eqn:hi;
        try solve_by_inversion. *)

       destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
       cbn in *.
       monad_unfold.
       repeat break_let.
       dosome.
       econstructor.
       eapply gen_ev_mapped; eauto.

    +
                        destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      try haaa.
      (*
      destruct ( map_get (st_sigmap a_st) p') eqn:hi;
        try solve_by_inversion. *)

       destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
       cbn in *.
       monad_unfold.
       repeat break_let.
       dosome.
       econstructor.
       eapply gen_ev_mapped; eauto.

    +
                              destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      try haaa.
      (*
      destruct ( map_get (st_sigmap a_st) p') eqn:hi;
        try solve_by_inversion. *)

       destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
       cbn in *.
       monad_unfold.
       repeat break_let.
       dosome.
       econstructor.
       eapply gen_ev_mapped; eauto.
  -
    
      
      
      
      
      
      

      
      
      
  -
    
      
      
      
      
      
      

      
      
      
      




      
      destruct (map_get (st_aspmap a_st) (p', n0));
        try solve_by_inversion.
      df.
      destruct e';
        try (
            cbn in *;
            monad_unfold;
            solve_by_inversion).
      cbn in *.
      monad_unfold.
      repeat break_let.
      dosome.
      destruct (map_get (st_aspmap a) (p', n)) eqn:hey;
        try solve_by_inversion.
      df.
      eapply gen_ev_mapped; eauto.
      ++
        reflexivity.
      ++
        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).
        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.
        destruct (map_get (st_aspmap a_st) (p', n0)) eqn:hi;
          try solve_by_inversion.
        df.

        destruct e';
          try (
              cbn in *;
              monad_unfold;
              solve_by_inversion).

        cbn in *.
        monad_unfold.
        repeat break_let.
        dosome.

        destruct (map_get (st_aspmap a) (p', n)) eqn:ho;
          try solve_by_inversion.
        eexists.
        df.
        econstructor.
        eassumption.
        
        
        
        
        

        
        eexists.
        econstructor.
        eassumption.
 *)





(*
Lemma gen_lseq_decomp :
  forall e e' e'' ee eee tr tr' tr'' st_trace3 st_trace4 p p' p'' pp ppp o o' o'' oo ooo a0 a1 et a_st a a2 x0 x o0 o1,
    build_comp a0 {| st_ev := e; st_trace := tr; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) ->
    build_comp a1 {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) ->
    gen_appraisal_comp e'' (eval (unanno a1) p' (eval (unanno a0) p et)) a_st = (Some x0, a) ->
    Ev_Shape e et -> (* TODO: need this? *)
    x0 {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |} =
    (o0, {| st_ev := ee; st_trace := st_trace3; st_pl := pp; st_store := oo |}) ->
    gen_appraisal_comp e' (eval (unanno a0) p et) a_st = (Some x, a2) ->
    x {| st_ev := mtc; st_trace := []; st_pl := 0; st_store := [] |} =
    (o1, {| st_ev := eee; st_trace := st_trace4; st_pl := ppp; st_store := ooo |}) ->
    exists l, st_trace3 = st_trace4 ++ l.
Proof.
  intros.
  Check gen_ev_shape.
  assert (Ev_Shape e'  (eval (unanno a0) p et)).
  eapply gen_ev_shape; eauto.
  assert (Ev_Shape e''  (eval (unanno a1) p' (eval (unanno a0) p et))).
  eapply gen_ev_shape; eauto.
  generalize dependent ee.
  generalize dependent eee.
  generalize dependent e.
  generalize dependent tr.
  generalize dependent tr'.
  generalize dependent tr''.
  generalize dependent st_trace3.
  generalize dependent st_trace4.
  generalize dependent p''.
  generalize dependent pp.
  generalize dependent ppp.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent o''.
  generalize dependent oo.
  generalize dependent ooo.
  generalize dependent a_st.
  generalize dependent a.
  generalize dependent a2.
  generalize dependent o1.
  generalize dependent o0.
  generalize dependent x0.
  generalize dependent x.
  generalize dependent e'.
  generalize dependent e''.
  generalize dependent p.
  generalize dependent p'.
  generalize dependent et.

  induction a0;
    destruct a1;
    intros.

(*
          
          induction e'';
            destruct  (eval (unanno a1) p' (eval (unanno a0) p et));
            try solve_by_inversion;
            intros.
          -
            

          evShapeFacts.

          cbn in *.
          monad_unfold.
          inv H1.
          inv H1.
          df.
          eexists
          invc H4.
          invc H5.
          exists st_trace3.
          simpl.
          reflexivity.
          -
            


          evShapeFacts.
          cbn in *.
          unfold bind in H4.
          repeat break_let.
          dosome.
          destruct (map_get (st_aspmap a_st) (n2, n1)); try solve_by_inversion.
          repeat find_inversion.

          eapply IHe'.
 *)        
  
Admitted.
*)
