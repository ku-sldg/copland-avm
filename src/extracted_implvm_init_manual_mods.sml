(*
<   > 

Warning: The following axioms must be realized in the extracted
code: MonadVM.do_hash Axioms_Io.toRemote Axioms_Io.remote_events
      MonadVM.do_sig MonadVM.encodeEv.
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

datatype aSP =
  CPY 
| ASPC nat (nat list) nat nat
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
| Uu nat (nat list) nat nat EvidenceT
| Gg nat EvidenceT
| Hh nat EvidenceT
| Nn nat
| Ss EvidenceT EvidenceT
| Pp EvidenceT EvidenceT

datatype ev =
  Copy nat nat
| Umeas nat nat nat (nat list) nat nat
| Sign nat nat EvidenceT
| Hash nat nat EvidenceT
| Req nat nat nat term EvidenceT
| Rpy nat nat nat EvidenceT
| Split nat nat
| Join nat nat

type range = (nat, nat) prod

datatype annoTerm =
  Aasp range aSP
| Aatt range nat annoTerm
| Alseq range annoTerm annoTerm
| Abseq range split annoTerm annoTerm
| Abpar range split annoTerm annoTerm

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

type evBits = nat list

datatype evC =
  Evc evBits EvidenceT

(** val mt_evc : evC **)

val mt_evc =
  Evc Nil Mt

(** val get_et : evC -> EvidenceT **)

fun get_et e = case e of
  Evc _ et => et

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

(** val toRemote : annoTerm -> nat -> evC -> evC **)

val toRemote =
  failwith "AXIOM TO BE REALIZED"

(** val remote_events : annoTerm -> nat -> ev list **)

val remote_events =
  failwith "AXIOM TO BE REALIZED"

datatype cvm_st =
  Mk_st evC (ev list) nat

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

(** val split_ev : nat -> split -> evC cVM **)

fun split_ev i sp =
  bind get_ev (fn e =>
    bind get_pl (fn p =>
      let val e1 = splitEv_l sp e in
      let val e2 = splitEv_r sp e in
      bind (put_ev e1) (fn _ =>
        bind (add_tracem (Cons (Split i p) Nil)) (fn _ => ret e2)) end end))

(** val call_ASP : nat -> nat list -> nat -> nat -> nat -> nat cVM **)

fun call_ASP i l tid tpl x =
  bind get_pl (fn p =>
    bind (add_tracem (Cons (Umeas x p i l tpl tid) Nil)) (fn _ => ret x))

(** val cons_asp_evt : nat -> evC -> nat -> nat list -> nat -> nat -> evC **)

fun cons_asp_evt x e i l tpl tid =
  let val Evc bits et = e in Evc (Cons x bits) (Uu i l tpl tid et) end

(** val invoke_ASP : nat -> nat list -> nat -> nat -> nat -> evC cVM **)

fun invoke_ASP i l tpl tid x =
  bind (call_ASP i l tid tpl x) (fn bs =>
    bind get_ev (fn e => ret (cons_asp_evt bs e i l tpl tid)))

(** val encodeEv : evC -> nat **)

val encodeEv =
  failwith "AXIOM TO BE REALIZED"

(** val do_sig : nat -> nat -> nat -> nat **)

val do_sig =
  failwith "AXIOM TO BE REALIZED"

(** val do_hash : nat -> nat -> nat **)

val do_hash =
  failwith "AXIOM TO BE REALIZED"

(** val tag_SIG : nat -> nat -> evC -> unit0 cVM **)

fun tag_SIG x p e =
  add_tracem (Cons (Sign x p (get_et e)) Nil)

(** val cons_gg : nat -> evC -> nat -> evC **)

fun cons_gg sig0 e p =
  let val Evc bits et = e in Evc (Cons sig0 bits) (Gg p et) end

(** val signEv : nat -> evC cVM **)

fun signEv x =
  bind get_pl (fn p =>
    bind get_ev (fn e =>
      bind (tag_SIG x p e) (fn _ =>
        ret (cons_gg (do_sig (encodeEv e) p x) e p))))

(** val tag_HSH : nat -> nat -> evC -> unit0 cVM **)

fun tag_HSH x p e =
  add_tracem (Cons (Hash x p (get_et e)) Nil)

(** val cons_hh : nat -> evC -> nat -> evC **)

fun cons_hh hsh e p =
  Evc (Cons hsh Nil) (Hh p (get_et e))

(** val hashEv : nat -> evC cVM **)

fun hashEv x =
  bind get_pl (fn p =>
    bind get_ev (fn e =>
      bind (tag_HSH x p e) (fn _ => ret (cons_hh (do_hash (encodeEv e) p) e p))))

(** val copyEv : nat -> evC cVM **)

fun copyEv x =
  bind get_pl (fn p =>
    bind (add_tracem (Cons (Copy x p) Nil)) (fn _ => get_ev))

(** val do_prim : nat -> aSP -> evC cVM **)

fun do_prim x a = case a of
  CPY => copyEv x
| ASPC asp_id l tpl tid => invoke_ASP asp_id l tpl tid x
| SIG => signEv x
| HSH => hashEv x

(** val sendReq : annoTerm -> nat -> nat -> unit0 cVM **)

fun sendReq t q reqi =
  bind get_pl (fn p =>
    bind get_ev (fn e =>
      add_tracem (Cons (Req reqi p q (unanno t) (get_et e)) Nil)))

(** val doRemote : annoTerm -> nat -> evC -> evC cVM **)

fun doRemote t q e =
  bind (add_tracem (remote_events t q)) (fn _ => ret (toRemote t q e))

(** val receiveResp : annoTerm -> nat -> nat -> evC cVM **)

fun receiveResp t q rpyi =
  bind get_pl (fn p =>
    bind get_ev (fn e =>
      bind (doRemote t q e) (fn e' =>
        bind (add_tracem (Cons (Rpy (pred rpyi) p q (get_et e')) Nil))
          (fn _ => ret e'))))

(** val ss_cons : evC -> evC -> evC **)

fun ss_cons e1 e2 =
  let val Evc bits1 et1 = e1 in
  let val Evc bits2 et2 = e2 in Evc (app bits1 bits2) (Ss et1 et2) end end

(** val pp_cons : evC -> evC -> evC **)

fun pp_cons e1 e2 =
  let val Evc bits1 et1 = e1 in
  let val Evc bits2 et2 = e2 in Evc (app bits1 bits2) (Pp et1 et2) end end

(** val join_seq : nat -> evC -> evC -> unit0 cVM **)

fun join_seq n e1 e2 =
  bind get_pl (fn p =>
    bind (put_ev (ss_cons e1 e2)) (fn _ => add_tracem (Cons (Join n p) Nil)))

(** val join_par : nat -> evC -> evC -> unit0 cVM **)

fun join_par n e1 e2 =
  bind get_pl (fn p =>
    bind (put_ev (pp_cons e1 e2)) (fn _ => add_tracem (Cons (Join n p) Nil)))

(** val copland_compile : annoTerm -> unit0 cVM **)

fun copland_compile t = case t of
  Aasp r a => let val Pair n _ = r in bind (do_prim n a) put_ev end
| Aatt r q t' =>
  let val Pair i j = r in
  bind (sendReq t' q i) (fn _ => bind (receiveResp t' q j) put_ev) end
| Alseq _ t1 t2 => bind (copland_compile t1) (fn _ => copland_compile t2)
| Abseq r sp t1 t2 =>
  let val Pair x y = r in
  bind (split_ev x sp) (fn e2 =>
    bind (copland_compile t1) (fn _ =>
      bind get_ev (fn e1r =>
        bind (put_ev e2) (fn _ =>
          bind (copland_compile t2) (fn _ =>
            bind get_ev (fn e2r => join_seq (pred y) e1r e2r)))))) end
| Abpar r sp t1 t2 =>
  let val Pair x y = r in
  bind (split_ev x sp) (fn e2 =>
    bind (copland_compile t1) (fn _ =>
      bind get_ev (fn e1r =>
        bind (put_ev e2) (fn _ =>
          bind (copland_compile t2) (fn _ =>
            bind get_ev (fn e2r => join_par (pred y) e1r e2r)))))) end

