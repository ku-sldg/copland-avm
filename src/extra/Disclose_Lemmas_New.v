Lemma term_discloses_respects_events : forall annt t p e r H2,
      annoP annt t -> 
      events_discloses annt p e r H2 ->
      term_discloses_to_remote t p e (r, H2) = true.
Proof.


(* by contrapositive of ^ *)
Lemma events_respects_term_disclosure: forall t p q e r annt,
    annoP annt t -> 

  (~ (term_discloses_to_remote t p e (q,r) = true)) ->

  ~ (events_discloses annt p e q r).
Proof.


Lemma events_respects_term_disclosure_aspid_enc: forall t p e i r annt,
    annoP annt t -> 

  ~ (term_discloses_aspid_to_remote_enc t p e i r) ->

  ~ (events_discloses_aspid_enc annt p e i r).
Proof.

Lemma cvm_implies_events: forall t annt e e' bits bits' p p' cvmi cvmi' cvm_tr ev ac ac',
    annoP_indexed annt t cvmi cvmi'->

    build_cvmP (copland_compile t)
         {| st_ev := evc bits e; st_trace := []; st_pl := p; st_evid := cvmi; st_AM_config := ac |} 
         (resultC tt) {| st_ev := evc bits' e'; st_trace := cvm_tr; st_pl := p'; st_evid := cvmi'; st_AM_config := ac' |} ->

    In ev cvm_tr ->

    events annt p e ev.



Definition cvm_trace_discloses_to_remote (tr:list Ev) (r:Plc) (e:EvidenceT) : Prop :=
  exists ev,
    (In ev tr) /\
    (
      (exists reqi reqp reqt, 
        ev = (req reqi reqp r reqt e)) \/ 
      (exists rpyi rpyp, 
        ev = (rpy rpyi r rpyp e))
    ).

Definition cvm_trace_discloses_aspid_to_remote_enc (tr:list Ev) (i:ASP_ID) (r:Plc) : Prop :=
    exists e,
        evsubt_asp_enc_bool e i r = true /\
        cvm_trace_discloses_to_remote tr r e.


Definition events_discloses (annt:AnnoTerm) (p:Plc) (e:EvidenceT) (r:Plc) (e':EvidenceT): Prop :=
        exists ev,
        (
            events annt p e ev /\
            (
            (exists reqi reqp reqt, 
                ev = (req reqi reqp r reqt e')) \/ 
            (exists rpyi rpyp, 
                ev = (rpy rpyi r rpyp e'))
            )
        ).


Definition events_discloses_aspid_enc (annt:AnnoTerm) (p:Plc) (e:EvidenceT) (i:ASP_ID) (r:Plc): Prop :=
  exists reqe,
     evsubt_asp_enc_bool reqe i r = true /\
     events_discloses annt p e r reqe.


(* Main Theorem *)
Theorem cvm_respects_term_disclosure_aspid_enc:
forall t p e i r atp bits bits' p' e' cvm_tr cvmi cvmi' annt ac ac',

annoP_indexed annt t cvmi cvmi' ->

~ (term_discloses_aspid_to_remote_enc t p e i r) ->

term_to_coreP t atp ->
build_cvmP atp
        (mk_st (evc bits e) [] p cvmi ac)
        (resultC tt)
        (mk_st (evc bits' e') cvm_tr p' cvmi' ac') ->

~ (cvm_trace_discloses_aspid_to_remote_enc cvm_tr i r).







Lemma cvm_respects_events_disclosure:
  forall t p e i r atp bits bits' p' e' cvm_tr cvmi cvmi' annt ac ac',
    
    annoP_indexed annt t cvmi cvmi' ->
    ~ (events_discloses annt p e i r) ->
    
    term_to_coreP t atp ->
    build_cvmP atp
               (mk_st (evc bits e) [] p cvmi ac)
               (resultC tt)
               (mk_st (evc bits' e') cvm_tr p' cvmi' ac') ->

    ~ (cvm_trace_discloses_to_remote cvm_tr i r).

Proof.
  unfold not in *; intros.
  apply H0.
  invc H3.
  destruct_conjs.
  unfold events_discloses.
  (*exists H4. *) exists x. (* exists H3. exists H5. exists H6. exists H7. *)
  split.
  invc H1.
  eapply cvm_implies_events.
  eassumption.
  eassumption.
  apply H3.
  eassumption.
Qed.


Check term_discloses_to_remote.

Lemma cvm_respects_term_disclosure:
  forall t p e i r atp bits bits' p' e' cvm_tr cvmi cvmi' annt ac ac',

    annoP_indexed annt t cvmi cvmi' ->

  ~ (term_discloses_to_remote t p e (r,i) = true) ->
  
  term_to_coreP t atp ->
  build_cvmP atp
             (mk_st (evc bits e) [] p cvmi ac)
             (resultC tt)
             (mk_st (evc bits' e') cvm_tr p' cvmi' ac') ->

  ~ (cvm_trace_discloses_to_remote cvm_tr r i).
Proof.
  intros.
  (*
  assert (exists annt, annoP_indexed annt t cvmi cvmi').
  {
    eapply can_annoP_indexed; eauto.
  }
  destruct_conjs.
   *)

  eapply cvm_respects_events_disclosure.
  
  eassumption.
  eapply events_respects_term_disclosure.
  invc H.
  econstructor.
  repeat eexists.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
Qed.