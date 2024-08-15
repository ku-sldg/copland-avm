(* Generalized appraisal implementation:  
    Top-level EvidenceT unbundling and appraisal ASP dispatch.   *)

Require Import ConcreteEvidenceT ErrorStMonad_Coq.

Require Import ErrorStringConstants Appraisal_Defs AM_St.

Require Import List.
Import ListNotations ErrNotation.



Definition peel_bs_am (ls:RawEv) : AM (BS * RawEv) :=
  match ls with
  | bs :: ls' => err_ret (bs, ls')
  | _ => am_failm (am_error errStr_peel_bs_am)
  end.

Fixpoint peel_n_am (n : nat) (ls : RawEv) : AM (RawEv * RawEv) :=
  match n with
  | 0 => err_ret ([], ls)
  | S n' =>
      match ls with
      | [] => am_failm (am_error errStr_peel_n_am)
      | x :: ls' =>
          v <- peel_n_am n' ls' ;;
          match v with
          | (ls1, ls2) => err_ret (x :: ls1, ls2)
          end
      end
  end.


Fixpoint gen_appraise_AM (et:EvidenceT) (ls:RawEv) : AM AppResultC :=
  match et with
  | mt_evt=> err_ret mtc_app
  | nonce_evt nid =>
    v <- (peel_bs_am ls) ;;
    match v with
      (bs, _) =>
      res <- checkNonce' nid bs ;;
      err_ret (nnc_app nid res)
    end

  | asp_evt p fwd params et' =>
    match fwd with
    | COMP => err_ret mtc_app (* TODO hash check *)
    | ENCR =>
      v <- peel_bs_am ls ;;
      match v with
        (bs, ls') => 
        decrypted_ls <- decrypt_bs_to_rawev' bs params et' ;;
        rest <- gen_appraise_AM et' decrypted_ls ;;
        err_ret (eec_app p params passed_bs rest)
      (* TODO: consider encoding success/failure  of decryption for bs param 
         (instead of default_bs)  *)
      end

    | (EXTD n) =>
      v <- peel_n_am n ls ;;
      match v with
        (rawEv, ls') => 
        v <- check_asp_EXTD' params p rawEv ls' ;;
        rest <- gen_appraise_AM et' ls' ;;
        err_ret (ggc_app p params v rest)
      end
    | KILL => err_ret mtc_app (* Do we ever reach this case? *)
    | KEEP => gen_appraise_AM et' ls (* Do we ever reach this case? *)
    end
  | split_evt et1 et2 => 
      x <- gen_appraise_AM et1 (firstn (et_size et1) ls) ;;
      y <- gen_appraise_AM et2 (skipn (et_size et1) ls) ;;
      err_ret (ssc_app x y)
    end.
