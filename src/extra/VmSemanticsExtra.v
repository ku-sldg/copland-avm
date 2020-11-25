(*
Lemma fafaf : forall t e e' e'' p p' p'' o o' o'' x y r s,
    well_formed t ->
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (None, {| st_ev := e'; st_trace := y; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := r; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := s; st_pl := p''; st_store := o'' |}) ->
    False.
Proof.
  
  induction t; intros.
  - destruct a;
      df;
      solve_by_inversion.
  -
    repeat (df; dohtac).
  -
    df.
    repeat break_match; try solve_by_inversion.
    +
      do_wf_pieces.       
      dohi'.
      df.
      eauto.
    +
      do_wf_pieces.  
      annogo.
      eauto.    
  -
    do_wf_pieces.
    df.
    repeat break_match;
      monad_unfold; allss;
        annogo;
        try dohi';
        eauto.        
  -
    do_wf_pieces.
    repeat (df; dohtac).
Defined.

Lemma fals : forall a e x y p o u v v' P,
    well_formed a ->
    build_comp a
               {|
                 st_ev := e;
                 st_trace := x;
                 st_pl := p;
                 st_store := o |} = (None, v) ->
    build_comp a
               {|
                 st_ev := e;
                 st_trace := y;
                 st_pl := p;
                 st_store := o |} = (Some u, v') ->
    P.
Proof.
  intros.
  exfalso.
  annogo.
  eapply fafaf; eauto.
Defined.

Ltac build_contra :=
  match goal with
  | [H: build_comp ?b {|
             st_ev := ?e;
             st_trace := _;
             st_pl := ?p;
             st_store := ?o |} = (Some _,_),
        H2: build_comp ?b {|
             st_ev := ?e;
             st_trace := _;
             st_pl := ?p;
             st_store := ?o |} = (None,_) |- _] => eapply fals with (a:=b); eauto
  end.
 *)

Lemma haha {A:Type} : forall (m:list A) l req rem rpy,
    m ++ (req :: rem ++ [rpy]) ++ l =
    m ++ [req] ++ rem ++ [rpy] ++ l.
Proof.
  intros.
  simpl.
  repeat rewrite <- app_assoc.
  simpl.
  reflexivity.
Defined.

Lemma store_get_set_fail_none : forall n e tr p o e1 v,
    get_store_at n
     {|
       st_ev := e;
       st_trace := tr;
       st_pl := p;
       st_store := map_set o n e1 |} =
    (None, v) ->
    False.
Proof.
  intros.
  unfold get_store_at in *.
  cbn in H.
  break_let.
  rewrite PeanoNat.Nat.eqb_refl in Heqp0.
  monad_unfold; repeat (break_match; allss); congruence.
Defined.

Lemma store_get_set : forall e tr p o n e1 e' v0,
    get_store_at n
      {|
        st_ev := e;
        st_trace := tr;
        st_pl := p;
        st_store := map_set o n e1 |} =
    (Some e', v0) ->
    e' = e1.
Proof.
  intros.
  monad_unfold; repeat (break_match; allss).
  unfold get_store_at in *.
  unfold get in *. simpl in *.
  cbn in H.
  break_let.
  rewrite PeanoNat.Nat.eqb_refl in Heqp0.
  monad_unfold; repeat (break_match; allss); congruence.
Defined.

(*
Lemma evshape_at : forall e es t n,
    Ev_Shape e es ->
    Ev_Shape (toRemote (unanno t) e) (Term.eval (unanno t) n es).
Proof.
Admitted.

Lemma evshape_par : forall e es a p,
    Ev_Shape e es ->
    Ev_Shape (parallel_att_vm_thread a e)
             (Term.eval (unanno a) p es).
Proof.
Admitted.
*)

Lemma record_congr :
  forall A,
    A =
    {| st_ev := st_ev A;
       st_trace := st_trace A;
       st_pl := st_pl A;
       st_store := st_store A|}.
Proof.
  intros A.
  destruct A.
  reflexivity.
Defined.

(*
Axiom para_eval_vm : forall t e,
    parallel_eval_thread (unanno t) e = parallel_att_vm_thread t e.
 *)

Lemma ssc_inv : forall e1 e1' e2 e2',
    e1 = e1' ->
    e2 = e2' ->
    ssc e1 e2 = ssc e1' e2'.
Proof.
  intros.
  congruence.
Defined.



(*
  Ltac df' :=
  repeat (cbn in *; unfold runSt in *; repeat break_let; repeat (monad_unfold; cbn in *; find_inversion); monad_unfold; repeat dunit). 
*)
