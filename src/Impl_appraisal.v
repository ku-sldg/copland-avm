Require Import Term ConcreteEvidence ErrorStMonad_Coq.

Require Import Example_Phrases_Demo.

Require Import ErrorStringConstants.

Require Import Appraisal_Defs Appraisal_IO_Stubs AM_Monad AM_St.

Require Import IO_Stubs Cvm_Run.

Require Import List.
Import ListNotations.



Definition peel_bs_am (ls:RawEv) : AM (BS * RawEv) :=
  match ls with
  | bs :: ls' => ret (bs, ls')
  | _ => am_failm (am_error errStr_peel_bs_am)
  end.

Fixpoint gen_appraise_AM (et:Evidence) (ls:RawEv) : AM AppResultC :=
  match et with
  | mt => ret mtc_app
  | nn nid =>
    v <- (peel_bs_am ls) ;;
    match v with
      (bs, _) =>
      res <- checkNonce' nid bs ;;
      ret (nnc_app nid res)
    end

  | uu p fwd params et' =>
    match fwd with
    | COMP => ret mtc_app (* TODO hash check *)
    | ENCR =>
      v <- peel_bs_am ls ;;
      match v with
        (bs, ls') => 
        decrypted_ls <- decrypt_bs_to_rawev' bs params et' ;;
        rest <- gen_appraise_AM et' decrypted_ls ;;
        ret (eec_app p params passed_bs rest)
      (* TODO: consider encoding success/failure  of decryption for bs param 
         (instead of default_bs)  *)
      end

    | EXTD =>
      v <- peel_bs_am ls ;;
      match v with
        (bs, ls') => 
        v <- check_asp_EXTD' params p bs ls' ;;
        rest <- gen_appraise_AM et' ls' ;;
        ret (ggc_app p params v rest)
      end
    | KILL => ret mtc_app (* Do we ever reach this case? *)
    | KEEP => gen_appraise_AM et' ls (* Do we ever reach this case? *)
    end
  | ss et1 et2 => 
      x <- gen_appraise_AM et1 (firstn (et_size et1) ls) ;;
      y <- gen_appraise_AM et2 (skipn (et_size et1) ls) ;;
      ret (ssc_app x y)
    end.
