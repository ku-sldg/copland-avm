Require Import Term IO_Stubs Cvm_Run.

Require Import AM_Monad StMonad_Coq Impl_appraisal privPolicy.


Require Import List.
Import ListNotations.



Definition am_check_auth_tok (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) : AM AppResultC :=
  match authTok with
  | evc auth_ev auth_et => 
    appres <-
    (match (requester_bound t fromPl authTok) with
     | false => failm
     | true => gen_appraise_AM auth_et auth_ev
     end) ;;
    ret appres
  end.

Definition am_serve_auth_tok_req (t:Term) (fromPl:Plc) (myPl:Plc) (authTok:ReqAuthTok) (init_ev:RawEv): AM RawEv :=
  match authTok with
  | evc auth_ev auth_et => 
    v <- am_check_auth_tok t fromPl authTok ;;
    match (andb (requester_bound t fromPl authTok) (appraise_auth_tok v)) with
    | true =>
      match (privPolicy fromPl t) with
      | true => ret (run_cvm_rawEv t myPl init_ev)
      | false => failm
      end
        
    | false => failm
    end
  end.


