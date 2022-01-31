 <   > 

Warning: The following axioms must be realized in the extracted
code: do_sig do_asp encodeEvRaw Axioms_Io.cvm_events parallel_vm_thread
      do_hash doRemote_session Term_Defs.BS.
 [extraction-axiom-to-realize,extraction]

module Main where

import qualified Prelude

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Plc = Prelude.Integer

type ASP_ID = Prelude.Integer

type TARG_ID = Prelude.Integer

type N_ID = Prelude.Integer

type Arg = Prelude.Integer

type Event_ID = Prelude.Integer

type BS = () -- AXIOM TO BE REALIZED
  

data ASP_PARAMS =
   Asp_paramsC ASP_ID (([]) Arg) Plc TARG_ID

data ASP =
   CPY
 | ASPC ASP_PARAMS
 | SIG
 | HSH

data SP =
   ALL
 | NONE

type Split = (,) SP SP

data Term =
   Asp ASP
 | Att Plc Term
 | Lseq Term Term
 | Bseq Split Term Term
 | Bpar Split Term Term

data Evidence =
   Mt
 | Uu ASP_PARAMS Plc Evidence
 | Gg Plc Evidence
 | Hh Plc Evidence
 | Nn N_ID
 | Ss Evidence Evidence
 | Pp Evidence Evidence

type RawEv = ([]) BS

data EvC =
   Evc RawEv Evidence

mt_evc :: EvC
mt_evc =
  Evc ([]) Mt

get_et :: EvC -> Evidence
get_et e =
  case e of {
   Evc _ et -> et}

get_bits :: EvC -> ([]) BS
get_bits e =
  case e of {
   Evc ls _ -> ls}

type Loc = Prelude.Integer

data Ev =
   Copy Prelude.Integer Plc
 | Umeas Prelude.Integer Plc ASP_ID (([]) Arg) Plc TARG_ID
 | Sign Prelude.Integer Plc Evidence
 | Hash Prelude.Integer Plc Evidence
 | Req Prelude.Integer Plc Plc Term Evidence
 | Rpy Prelude.Integer Plc Plc Evidence
 | Split0 Prelude.Integer Plc
 | Join Prelude.Integer Plc
 | Cvm_thread_start Loc Plc Term Evidence
 | Cvm_thread_end Loc

data AnnoTermPar =
   Aasp_par ASP
 | Aatt_par Plc Term
 | Alseq_par AnnoTermPar AnnoTermPar
 | Abseq_par Split AnnoTermPar AnnoTermPar
 | Abpar_par Loc Split AnnoTermPar Term

splitEv_l :: Split -> EvC -> EvC
splitEv_l sp e =
  case sp of {
   (,) s _ -> case s of {
               ALL -> e;
               NONE -> mt_evc}}

splitEv_r :: Split -> EvC -> EvC
splitEv_r sp e =
  case sp of {
   (,) _ s0 -> case s0 of {
                ALL -> e;
                NONE -> mt_evc}}

do_asp :: ASP_PARAMS -> Plc -> BS
do_asp =
  Prelude.error "AXIOM TO BE REALIZED"

encodeEvRaw :: RawEv -> BS
encodeEvRaw =
  Prelude.error "AXIOM TO BE REALIZED"

do_sig :: BS -> Plc -> BS
do_sig =
  Prelude.error "AXIOM TO BE REALIZED"

do_hash :: BS -> Plc -> BS
do_hash =
  Prelude.error "AXIOM TO BE REALIZED"

doRemote_session :: Term -> Plc -> EvC -> EvC
doRemote_session =
  Prelude.error "AXIOM TO BE REALIZED"

parallel_vm_thread :: Loc -> Term -> Plc -> EvC -> EvC
parallel_vm_thread =
  Prelude.error "AXIOM TO BE REALIZED"

cvm_events :: Term -> Plc -> Evidence -> ([]) Ev
cvm_events =
  Prelude.error "AXIOM TO BE REALIZED"

cons_uu :: BS -> EvC -> ASP_PARAMS -> Plc -> EvC
cons_uu x e params mpl =
  case e of {
   Evc bits et -> Evc ((:) x bits) (Uu params mpl et)}

cons_sig :: BS -> EvC -> Plc -> EvC
cons_sig sig e p =
  case e of {
   Evc bits et -> Evc ((:) sig bits) (Gg p et)}

cons_hh :: BS -> EvC -> Plc -> EvC
cons_hh hsh e p =
  case e of {
   Evc _ et -> Evc ((:) hsh ([])) (Hh p et)}

ss_cons :: EvC -> EvC -> EvC
ss_cons e1 e2 =
  case e1 of {
   Evc bits1 et1 ->
    case e2 of {
     Evc bits2 et2 -> Evc (app bits1 bits2) (Ss et1 et2)}}

pp_cons :: EvC -> EvC -> EvC
pp_cons e1 e2 =
  case e1 of {
   Evc bits1 et1 ->
    case e2 of {
     Evc bits2 et2 -> Evc (app bits1 bits2) (Pp et1 et2)}}

encodeEvBits :: EvC -> BS
encodeEvBits e =
  case e of {
   Evc bits _ -> encodeEvRaw bits}

data Cvm_st =
   Mk_st EvC (([]) Ev) Plc Event_ID

st_ev :: Cvm_st -> EvC
st_ev c =
  case c of {
   Mk_st st_ev0 _ _ _ -> st_ev0}

st_trace :: Cvm_st -> ([]) Ev
st_trace c =
  case c of {
   Mk_st _ st_trace0 _ _ -> st_trace0}

st_pl :: Cvm_st -> Plc
st_pl c =
  case c of {
   Mk_st _ _ st_pl0 _ -> st_pl0}

st_evid :: Cvm_st -> Event_ID
st_evid c =
  case c of {
   Mk_st _ _ _ st_evid0 -> st_evid0}

type St s a = s -> (,) (Prelude.Maybe a) s

ret :: a2 -> St a1 a2
ret a s =
  (,) (Prelude.Just a) s

bind :: (St a1 a2) -> (a2 -> St a1 a3) -> St a1 a3
bind m f s =
  case m s of {
   (,) a s' ->
    case a of {
     Prelude.Just v -> f v s';
     Prelude.Nothing -> (,) Prelude.Nothing s'}}

modify :: (a1 -> a1) -> St a1 ()
modify f s =
  (,) (Prelude.Just ()) (f s)

put :: a1 -> St a1 ()
put s _ =
  (,) (Prelude.Just ()) s

get :: St a1 a1
get s =
  (,) (Prelude.Just s) s

type CVM a = St Cvm_st a

put_ev :: EvC -> CVM ()
put_ev e =
  bind get (\st ->
    let {tr' = st_trace st} in
    let {p' = st_pl st} in let {i = st_evid st} in put (Mk_st e tr' p' i))

get_ev :: CVM EvC
get_ev =
  bind get (\st -> ret (st_ev st))

get_pl :: CVM Plc
get_pl =
  bind get (\st -> ret (st_pl st))

inc_id :: CVM Event_ID
inc_id =
  bind get (\st ->
    let {tr' = st_trace st} in
    let {e' = st_ev st} in
    let {p' = st_pl st} in
    let {i = st_evid st} in
    bind (put (Mk_st e' tr' p' ((Prelude.+) i (succ 0)))) (\_ -> ret i))

add_trace :: (([]) Ev) -> Cvm_st -> Cvm_st
add_trace tr' pat =
  case pat of {
   Mk_st e tr p i -> Mk_st e (app tr tr') p i}

add_tracem :: (([]) Ev) -> CVM ()
add_tracem tr =
  modify (add_trace tr)

split_ev :: Split -> CVM ((,) EvC EvC)
split_ev sp =
  bind get_ev (\e ->
    bind get_pl (\p ->
      bind inc_id (\i ->
        let {e1 = splitEv_l sp e} in
        let {e2 = splitEv_r sp e} in
        bind (add_tracem ((:) (Split0 i p) ([]))) (\_ -> ret ((,) e1 e2)))))

tag_ASP :: ASP_PARAMS -> Plc -> CVM Event_ID
tag_ASP params mpl =
  case params of {
   Asp_paramsC i l tpl tid ->
    bind inc_id (\x ->
      bind (add_tracem ((:) (Umeas x mpl i l tpl tid) ([]))) (\_ -> ret x))}

invoke_ASP :: ASP_PARAMS -> CVM EvC
invoke_ASP params =
  bind get_ev (\e ->
    bind get_pl (\p ->
      bind (tag_ASP params p) (\_ ->
        let {bs = do_asp params p} in ret (cons_uu bs e params p))))

tag_SIG :: Plc -> EvC -> CVM Event_ID
tag_SIG p e =
  bind inc_id (\x ->
    bind (add_tracem ((:) (Sign x p (get_et e)) ([]))) (\_ -> ret x))

signEv :: CVM EvC
signEv =
  bind get_pl (\p ->
    bind get_ev (\e ->
      bind (tag_SIG p e) (\_ ->
        let {bs = do_sig (encodeEvBits e) p} in ret (cons_sig bs e p))))

tag_HSH :: Plc -> EvC -> CVM Event_ID
tag_HSH p e =
  bind inc_id (\x ->
    bind (add_tracem ((:) (Hash x p (get_et e)) ([]))) (\_ -> ret x))

hashEv :: CVM EvC
hashEv =
  bind get_pl (\p ->
    bind get_ev (\e ->
      bind (tag_HSH p e) (\_ ->
        let {bs = do_hash (encodeEvBits e) p} in ret (cons_hh bs e p))))

copyEv :: CVM EvC
copyEv =
  bind get_pl (\p ->
    bind inc_id (\x ->
      bind (add_tracem ((:) (Copy x p) ([]))) (\_ -> get_ev)))

do_prim :: ASP -> CVM EvC
do_prim a =
  case a of {
   CPY -> copyEv;
   ASPC params -> invoke_ASP params;
   SIG -> signEv;
   HSH -> hashEv}

event_id_span :: Term -> Prelude.Integer
event_id_span t =
  case t of {
   Asp _ -> succ 0;
   Att _ x -> (Prelude.+) (succ (succ 0)) (event_id_span x);
   Lseq x y -> (Prelude.+) (event_id_span x) (event_id_span y);
   Bseq _ x y ->
    (Prelude.+) ((Prelude.+) (succ (succ 0)) (event_id_span x))
      (event_id_span y);
   Bpar _ x y ->
    (Prelude.+) ((Prelude.+) (succ (succ 0)) (event_id_span x))
      (event_id_span y)}

inc_remote_event_ids :: Term -> CVM ()
inc_remote_event_ids t =
  bind get (\st ->
    let {tr' = st_trace st} in
    let {e' = st_ev st} in
    let {p' = st_pl st} in
    let {i = st_evid st} in
    let {new_i = (Prelude.+) i (event_id_span t)} in
    put (Mk_st e' tr' p' new_i))

tag_REQ :: Term -> Plc -> Plc -> EvC -> CVM ()
tag_REQ t p q e =
  bind inc_id (\reqi -> add_tracem ((:) (Req reqi p q t (get_et e)) ([])))

tag_RPY :: Plc -> Plc -> EvC -> CVM ()
tag_RPY p q e =
  bind inc_id (\rpyi -> add_tracem ((:) (Rpy rpyi p q (get_et e)) ([])))

remote_session :: Term -> Plc -> Plc -> EvC -> CVM EvC
remote_session t p q e =
  bind (tag_REQ t p q e) (\_ ->
    let {e' = doRemote_session t q e} in
    bind (add_tracem (cvm_events t q (get_et e))) (\_ ->
      bind (inc_remote_event_ids t) (\_ -> ret e')))

doRemote :: Term -> Plc -> EvC -> CVM EvC
doRemote t q e =
  bind get_pl (\p ->
    bind (remote_session t p q e) (\e' ->
      bind (tag_RPY p q e') (\_ -> ret e')))

join_seq :: EvC -> EvC -> CVM ()
join_seq e1 e2 =
  bind get_pl (\p ->
    bind inc_id (\n ->
      bind (put_ev (ss_cons e1 e2)) (\_ -> add_tracem ((:) (Join n p) ([])))))

do_start_par_thread :: Loc -> Term -> RawEv -> CVM ()
do_start_par_thread _ _ _ =
  ret ()

start_par_thread :: Loc -> Term -> EvC -> CVM ()
start_par_thread loc t e =
  bind get_pl (\p ->
    bind (do_start_par_thread loc t (get_bits e)) (\_ ->
      add_tracem ((:) (Cvm_thread_start loc p t (get_et e)) ([]))))

do_wait_par_thread :: Loc -> Term -> Plc -> EvC -> CVM EvC
do_wait_par_thread loc t p e =
  ret (parallel_vm_thread loc t p e)

wait_par_thread :: Loc -> Term -> EvC -> CVM EvC
wait_par_thread loc t e =
  bind get_pl (\p ->
    bind (do_wait_par_thread loc t p e) (\e' ->
      bind (add_tracem ((:) (Cvm_thread_end loc) ([]))) (\_ ->
        bind (inc_remote_event_ids t) (\_ -> ret e'))))

join_par :: EvC -> EvC -> CVM ()
join_par e1 e2 =
  bind get_pl (\p ->
    bind inc_id (\n ->
      bind (put_ev (pp_cons e1 e2)) (\_ -> add_tracem ((:) (Join n p) ([])))))

copland_compile :: AnnoTermPar -> CVM ()
copland_compile t =
  case t of {
   Aasp_par a -> bind (do_prim a) put_ev;
   Aatt_par q t' -> bind get_ev (\e -> bind (doRemote t' q e) put_ev);
   Alseq_par t1 t2 -> bind (copland_compile t1) (\_ -> copland_compile t2);
   Abseq_par sp t1 t2 ->
    bind (split_ev sp) (\pr ->
      case pr of {
       (,) e1 e2 ->
        bind (put_ev e1) (\_ ->
          bind (copland_compile t1) (\_ ->
            bind get_ev (\e1r ->
              bind (put_ev e2) (\_ ->
                bind (copland_compile t2) (\_ ->
                  bind get_ev (\e2r -> join_seq e1r e2r))))))});
   Abpar_par loc sp t1 t2 ->
    bind (split_ev sp) (\pr ->
      case pr of {
       (,) e1 e2 ->
        bind (start_par_thread loc t2 e2) (\_ ->
          bind (put_ev e1) (\_ ->
            bind (copland_compile t1) (\_ ->
              bind get_ev (\e1r ->
                bind (wait_par_thread loc t2 e2) (\e2r -> join_par e1r e2r)))))})}


