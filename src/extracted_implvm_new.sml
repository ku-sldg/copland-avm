(*
Warning: The following axioms must be realized in the extracted
code: MonadVM.do_hash Axioms_Io.parallel_vm_thread ConcreteEvidenceT.BS
      MonadVM.encodeEvBits Axioms_Io.cvm_events Axioms_Io.doRemote_session
      MonadVM.do_sig MonadVM.do_asp.
 [extraction-axiom-to-realize,extraction]
*)

datatype unit0 =
  Tt 

datatype nat =
  O 
| S nat

datatype 'a option =
  Some 'a
| None 

datatype ('a, 'b) prod =
  Pair 'a 'b

datatype 'a list =
  Nil 
| Cons 'a ('a list)

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

fun app l m =
  case l of
    Nil => m
  | Cons a l1 => Cons a (app l1 m)

(** val pred : nat -> nat **)

fun pred n = case n of
  O => n
| S u => u

datatype aSP_PARAMS =
  Asp_paramsC nat (nat list) nat nat

datatype aSP =
  CPY 
| ASPC aSP_PARAMS
| SIG 
| HSH 

datatype sP =
  ALL 
| NONE 

type split = (sP, sP) prod

datatype term =
  Asp aSP
| Att nat term
| Lseq term term
| Bseq split term term
| Bpar split term term

datatype EvidenceT =
  Mt 
| Uu aSP_PARAMS nat EvidenceT
| Gg nat EvidenceT
| Hh nat EvidenceT
| Nn nat
| Ss EvidenceT EvidenceT
| Pp EvidenceT EvidenceT

type range = (nat, nat) prod

datatype annoTerm =
  Aasp range aSP
| Aatt range nat annoTerm
| Alseq range annoTerm annoTerm
| Abseq range split annoTerm annoTerm
| Abpar range split annoTerm annoTerm

type loc = nat

datatype ev =
  Copy nat nat
| Umeas nat nat nat (nat list) nat nat
| Sign nat nat EvidenceT
| Hash nat nat EvidenceT
| Req nat nat nat term EvidenceT
| Rpy nat nat nat EvidenceT
| Split nat nat
| Cvm_thread_start loc nat annoTerm EvidenceT
| Join nat nat
| Cvm_thread_end loc

datatype annoTermPar =
  Aasp_par range aSP
| Aatt_par range nat annoTerm
| Alseq_par range annoTermPar annoTermPar
| Abseq_par range split annoTermPar annoTermPar
| Abpar_par range loc split annoTermPar annoTerm

(** val unanno : annoTerm -> term **)

fun unanno a = case a of
  Aasp _ a0 => Asp a0
| Aatt _ p t => Att p (unanno t)
| Alseq _ a1 a2 => Lseq (unanno a1) (unanno a2)
| Abseq _ spl a1 a2 => Bseq spl (unanno a1) (unanno a2)
| Abpar _ spl a1 a2 => Bpar spl (unanno a1) (unanno a2)

type ('s, 'a) st = 's -> ('a option, 's) prod

(** val ret : 'a2 -> ('a1, 'a2) st **)

fun ret a s =
  Pair (Some a) s

(** val bind : ('a1, 'a2) st -> ('a2 -> ('a1, 'a3) st) -> ('a1, 'a3) st **)

fun bind m f s =
  let val Pair a s' = m s in
  (case a of
     Some v => f v s'
   | None => Pair None s') end

(** val modify : ('a1 -> 'a1) -> ('a1, unit0) st **)

fun modify f s =
  Pair (Some Tt) (f s)

(** val put : 'a1 -> ('a1, unit0) st **)

fun put s _ =
  Pair (Some Tt) s

(** val get : ('a1, 'a1) st **)

fun get s =
  Pair (Some s) s

type bS (* AXIOM TO BE REALIZED *)

type rawEv = bS list

datatype evC =
  Evc rawEv EvidenceT

(** val mt_evc : evC **)

val mt_evc =
  Evc Nil Mt

(** val get_et : evC -> EvidenceT **)

fun get_et e = case e of
  Evc _ et => et

(** val get_bits : evC -> bS list **)

fun get_bits e = case e of
  Evc ls _ => ls

(** val splitEv_l : split -> evC -> evC **)

fun splitEv_l sp e =
  let val Pair s _ = sp in (case s of
                              ALL => e
                            | NONE => mt_evc) end

(** val splitEv_r : split -> evC -> evC **)

fun splitEv_r sp e =
  let val Pair _ s0 = sp in (case s0 of
                               ALL => e
                             | NONE => mt_evc) end

datatype cvm_st =
  Mk_st evC (ev list) nat

(** val doRemote_session : annoTerm -> nat -> evC -> evC **)

val doRemote_session =
  failwith "AXIOM TO BE REALIZED"

(** val parallel_vm_thread : loc -> annoTerm -> nat -> evC -> evC **)

val parallel_vm_thread =
  failwith "AXIOM TO BE REALIZED"

(** val cvm_events : annoTerm -> nat -> EvidenceT -> ev list **)

val cvm_events =
  failwith "AXIOM TO BE REALIZED"

type event_ID = nat

type 'a cVM = (cvm_st, 'a) st

(** val put_ev : evC -> unit0 cVM **)

fun put_ev e =
  bind get (fn st0 =>
    let val tr' = let val Mk_st _ st_trace _ = st0 in st_trace end in
    let val p' = let val Mk_st _ _ st_pl = st0 in st_pl end in
    put (Mk_st e tr' p') end end)

(** val get_ev : evC cVM **)

val get_ev =
  bind get (fn st0 => ret (let val Mk_st st_ev _ _ = st0 in st_ev end))

(** val get_pl : nat cVM **)

val get_pl =
  bind get (fn st0 => ret (let val Mk_st _ _ st_pl = st0 in st_pl end))

(** val add_trace : ev list -> cvm_st -> cvm_st **)

fun add_trace tr' pat =
  let val Mk_st e tr p = pat in Mk_st e (app tr tr') p end

(** val add_tracem : ev list -> unit0 cVM **)

fun add_tracem tr =
  modify (add_trace tr)

(** val split_ev : event_ID -> split -> (evC, evC) prod cVM **)

fun split_ev i sp =
  bind get_ev (fn e =>
    bind get_pl (fn p =>
      let val e1 = splitEv_l sp e in
      let val e2 = splitEv_r sp e in
      bind (add_tracem (Cons (Split i p) Nil)) (fn _ => ret (Pair e1 e2)) end end))

(** val do_asp : aSP_PARAMS -> nat -> event_ID -> bS **)

val do_asp =
  failwith "AXIOM TO BE REALIZED"

(** val tag_ASP : aSP_PARAMS -> nat -> event_ID -> unit0 cVM **)

fun tag_ASP params mpl x =
  let val Asp_paramsC i l tpl tid = params in
  add_tracem (Cons (Umeas x mpl i l tpl tid) Nil) end

(** val cons_asp_evt : bS -> evC -> aSP_PARAMS -> nat -> evC **)

fun cons_asp_evt x e params mpl =
  let val Evc bits et = e in Evc (Cons x bits) (Uu params mpl et) end

(** val invoke_ASP : aSP_PARAMS -> event_ID -> evC cVM **)

fun invoke_ASP params x =
  bind get_ev (fn e =>
    bind get_pl (fn p =>
      bind (tag_ASP params p x) (fn _ =>
        ret (cons_asp_evt (do_asp params p x) e params p))))

(** val encodeEvBits : evC -> bS **)

val encodeEvBits =
  failwith "AXIOM TO BE REALIZED"

(** val do_sig : bS -> nat -> event_ID -> bS **)

val do_sig =
  failwith "AXIOM TO BE REALIZED"

(** val do_hash : bS -> nat -> bS **)

val do_hash =
  failwith "AXIOM TO BE REALIZED"

(** val tag_SIG : event_ID -> nat -> evC -> unit0 cVM **)

fun tag_SIG x p e =
  add_tracem (Cons (Sign x p (get_et e)) Nil)

(** val cons_sig : bS -> evC -> nat -> evC **)

fun cons_sig sig0 e p =
  let val Evc bits et = e in Evc (Cons sig0 bits) (Gg p et) end

(** val signEv : event_ID -> evC cVM **)

fun signEv x =
  bind get_pl (fn p =>
    bind get_ev (fn e =>
      bind (tag_SIG x p e) (fn _ =>
        ret (cons_sig (do_sig (encodeEvBits e) p x) e p))))

(** val tag_HSH : event_ID -> nat -> evC -> unit0 cVM **)

fun tag_HSH x p e =
  add_tracem (Cons (Hash x p (get_et e)) Nil)

(** val cons_hh : bS -> evC -> nat -> evC **)

fun cons_hh hsh e p =
  let val Evc _ et = e in Evc (Cons hsh Nil) (Hh p et) end

(** val hashEv : event_ID -> evC cVM **)

fun hashEv x =
  bind get_pl (fn p =>
    bind get_ev (fn e =>
      bind (tag_HSH x p e) (fn _ =>
        ret (cons_hh (do_hash (encodeEvBits e) p) e p))))

(** val copyEv : event_ID -> evC cVM **)

fun copyEv x =
  bind get_pl (fn p =>
    bind (add_tracem (Cons (Copy x p) Nil)) (fn _ => get_ev))

(** val do_prim : event_ID -> aSP -> evC cVM **)

fun do_prim x a = case a of
  CPY => copyEv x
| ASPC params => invoke_ASP params x
| SIG => signEv x
| HSH => hashEv x

(** val tag_REQ : annoTerm -> nat -> nat -> evC -> event_ID -> unit0 cVM **)

fun tag_REQ t p q e reqi =
  add_tracem (Cons (Req reqi p q (unanno t) (get_et e)) Nil)

(** val tag_RPY : nat -> nat -> evC -> event_ID -> unit0 cVM **)

fun tag_RPY p q e rpyi =
  add_tracem (Cons (Rpy (pred rpyi) p q (get_et e)) Nil)

(** val remote_session :
    annoTerm -> nat -> nat -> evC -> event_ID -> evC cVM **)

fun remote_session t p q e reqi =
  bind (tag_REQ t p q e reqi) (fn _ =>
    let val e' = doRemote_session t q e in
    bind (add_tracem (cvm_events t q (get_et e))) (fn _ => ret e') end)

(** val doRemote :
    annoTerm -> nat -> evC -> event_ID -> event_ID -> evC cVM **)

fun doRemote t q e reqi rpyi =
  bind get_pl (fn p =>
    bind (remote_session t p q e reqi) (fn e' =>
      bind (tag_RPY p q e' rpyi) (fn _ => ret e')))

(** val ss_cons : evC -> evC -> evC **)

fun ss_cons e1 e2 =
  let val Evc bits1 et1 = e1 in
  let val Evc bits2 et2 = e2 in Evc (app bits1 bits2) (Ss et1 et2) end end

(** val pp_cons : evC -> evC -> evC **)

fun pp_cons e1 e2 =
  let val Evc bits1 et1 = e1 in
  let val Evc bits2 et2 = e2 in Evc (app bits1 bits2) (Pp et1 et2) end end

(** val join_seq : event_ID -> evC -> evC -> unit0 cVM **)

fun join_seq n e1 e2 =
  bind get_pl (fn p =>
    bind (put_ev (ss_cons e1 e2)) (fn _ =>
      add_tracem (Cons (Join (pred n) p) Nil)))

(** val do_start_par_thread : loc -> annoTerm -> rawEv -> unit0 cVM **)

fun do_start_par_thread _ _ _ =
  ret Tt

(** val start_par_thread : loc -> annoTerm -> evC -> unit0 cVM **)

fun start_par_thread loc0 t e =
  bind get_pl (fn p =>
    bind (do_start_par_thread loc0 t (get_bits e)) (fn _ =>
      add_tracem (Cons (Cvm_thread_start loc0 p t (get_et e)) Nil)))

(** val do_wait_par_thread : loc -> annoTerm -> nat -> evC -> evC cVM **)

fun do_wait_par_thread loc0 t p e =
  ret (parallel_vm_thread loc0 t p e)

(** val wait_par_thread : loc -> annoTerm -> evC -> evC cVM **)

fun wait_par_thread loc0 t e =
  bind get_pl (fn p =>
    bind (do_wait_par_thread loc0 t p e) (fn e' =>
      bind (add_tracem (Cons (Cvm_thread_end loc0) Nil)) (fn _ => ret e')))

(** val join_par : event_ID -> evC -> evC -> unit0 cVM **)

fun join_par n e1 e2 =
  bind get_pl (fn p =>
    bind (put_ev (pp_cons e1 e2)) (fn _ =>
      add_tracem (Cons (Join (pred n) p) Nil)))

(** val copland_compile : annoTermPar -> unit0 cVM **)

fun copland_compile t = case t of
  Aasp_par r a => let val Pair n _ = r in bind (do_prim n a) put_ev end
| Aatt_par r q t' =>
  let val Pair reqi rpyi = r in
  bind get_ev (fn e => bind (doRemote t' q e reqi rpyi) put_ev) end
| Alseq_par _ t1 t2 => bind (copland_compile t1) (fn _ => copland_compile t2)
| Abseq_par r sp t1 t2 =>
  let val Pair x y = r in
  bind (split_ev x sp) (fn pr =>
    let val Pair e1 e2 = pr in
    bind (put_ev e1) (fn _ =>
      bind (copland_compile t1) (fn _ =>
        bind get_ev (fn e1r =>
          bind (put_ev e2) (fn _ =>
            bind (copland_compile t2) (fn _ =>
              bind get_ev (fn e2r => join_seq y e1r e2r)))))) end) end
| Abpar_par r loc0 sp t1 t2 =>
  let val Pair x y = r in
  bind (split_ev x sp) (fn pr =>
    let val Pair e1 e2 = pr in
    bind (start_par_thread loc0 t2 e2) (fn _ =>
      bind (put_ev e1) (fn _ =>
        bind (copland_compile t1) (fn _ =>
          bind get_ev (fn e1r =>
            bind (wait_par_thread loc0 t2 e2) (fn e2r => join_par y e1r e2r))))) end) end

