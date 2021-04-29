open preamble;
open optionTheory
     rich_listTheory;
open endpoint_to_payloadTheory;
open payloadLangTheory
     payloadSemTheory
     payloadPropsTheory
     payload_to_cakemlTheory
     payloadCongTheory;
open comms_ffi_modelTheory
     comms_ffi_propsTheory
     comms_ffi_eqTheory
     comms_ffi_rec_characTheory
     comms_ffi_consTheory;
open evaluate_toolsTheory
     ckExp_EquivTheory;
open evaluate_rwLib
     state_tacticLib;
open evaluateTheory terminationTheory ml_translatorTheory
     ml_progTheory evaluatePropsTheory namespaceTheory
     semanticPrimitivesTheory ffiTheory;

open bigSmallEquivTheory smallStepHelpTheory smallStepTheory
     abstractCompilationTheory

open hide

val _ = new_theory "payload_to_cakemlProof";

val _ = temp_delsimps ["NORMEQ_CONV"];

val _ = set_grammar_ancestry
  ["endpoint_to_payload",
   "payloadCong","payloadLang","payloadSem","payloadProps",
   "payload_to_cakeml","comms_ffi_model","comms_ffi_props",
   "comms_ffi_eq","comms_ffi_rec_charac","comms_ffi_cons",
   "evaluate_tools", "ckExp_Equiv","termination",
   "ml_translator", "ml_prog", "evaluateProps", "namespace",
   "semanticPrimitives", "abstractCompilation"];
val _ = install_hidepp()

fun SRULE ths = SIMP_RULE (srw_ss()) ths

fun under_abs_path_unbeta_conv p t =
  let val(v,bod) = dest_abs t
  in
    ABS_CONV (PATH_CONV p (UNBETA_CONV v))
  end t

fun pull_namedexvar_conv s t =
  let val (v,bod) = dest_exists t
      val (vnm,_) = dest_var v
  in
    if vnm = s then raise UNCHANGED
    else (BINDER_CONV (pull_namedexvar_conv s) THENC SWAP_EXISTS_CONV) t
  end

fun pull_namedallvar_conv s t =
  let val (v,bod) = dest_forall t
      val (vnm,_) = dest_var v
  in
    if vnm = s then raise UNCHANGED
    else (BINDER_CONV (pull_namedallvar_conv s) THENC SWAP_FORALL_CONV) t
  end

fun underEXs f th =
  case total dest_exists $ concl th of
    NONE => f th
  | SOME (v,bod) => ASSUME bod |> underEXs f |> SIMPLE_EXISTS v |> CHOOSE(v,th)

fun atcj i f th =
 let
   val ths0 = CONJUNCTS th
   val ths = mapi (fn j => fn th => if i = j + 1 then f th else th) ths0
 in
   LIST_CONJ ths
 end

Theorem do_eq_def[local,simp] = terminationTheory.do_eq_def

Theorem ffi_eq_REFL[simp]:
  ffi_eq c s s
Proof
  ‘equivalence (ffi_eq c)’ by simp[ffi_eq_equivRel] >>
  fs[equivalence_def, reflexive_def]
QED

Theorem ffi_eq_SYM:
  ffi_eq c s1 s2 ⇔ ffi_eq c s2 s1
Proof
  ‘equivalence (ffi_eq c)’ by simp[ffi_eq_equivRel] >>
  fs[equivalence_def, symmetric_def]
QED

Theorem ffi_eq_TRANS:
  ffi_eq c s1 s2 ∧ ffi_eq c s2 s3 ⇒ ffi_eq c s1 s3
Proof
  ‘equivalence (ffi_eq c)’ by simp[ffi_eq_equivRel] >>
  fs[equivalence_def, transitive_def] >> metis_tac[]
QED

Definition pletrec_vars_ok_def[simp]:
  pletrec_vars_ok Nil = T ∧
  pletrec_vars_ok (Send dest var i e) = pletrec_vars_ok e ∧
  pletrec_vars_ok (Receive src destvar acc e) = pletrec_vars_ok e ∧
  pletrec_vars_ok (IfThen v e1 e2) = (pletrec_vars_ok e1 ∧ pletrec_vars_ok e2) ∧
  pletrec_vars_ok (Let var f vars e) = pletrec_vars_ok e ∧
  pletrec_vars_ok (Letrec fnm args e) = (pletrec_vars_ok e ∧ ALL_DISTINCT args)∧
  pletrec_vars_ok (FCall _ _) = T ∧
  pletrec_vars_ok (Fix _ e) = pletrec_vars_ok e
End

Definition cletrec_vars_ok_def[simp]:
  cletrec_vars_ok (Closure params (funs,bindings) body) =
  (pletrec_vars_ok body ∧ EVERY cletrec_vars_ok (MAP SND funs))
Termination
  WF_REL_TAC ‘measure(closure_size)’ >>
  simp[MEM_MAP,PULL_EXISTS] >>
  simp[FORALL_PROD] >> rw[] >>
  drule closure_size_MEM >>
  intLib.COOPER_TAC
End

Theorem pletrec_vars_ok_dsubst:
  ∀e e' dn.
  pletrec_vars_ok e ∧ pletrec_vars_ok e' ⇒
  pletrec_vars_ok (dsubst e dn e')
Proof
  Induct_on ‘e’ >> gvs[dsubst_def] >>
  rw[]
QED

Theorem letrec_vars_ok_trans_pres:
  trans conf (NEndpoint p s c) α (NEndpoint p' s' c') ∧
  pletrec_vars_ok c ∧
  EVERY cletrec_vars_ok (MAP SND s.funs)
  ⇒
  pletrec_vars_ok c' ∧
  EVERY cletrec_vars_ok (MAP SND s'.funs)
Proof
  rw[Once trans_cases] >>
  gvs[pletrec_vars_ok_dsubst,ETA_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  res_tac >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

val WORD8 = “WORD:word8 -> v -> bool”;
Overload WORD8 = “WORD:word8 -> v -> bool”;
Overload DATUM[local] = “LIST_TYPE WORD8”;
Type plffi[local,pp] = “:string # (string |-> word8 list list) # network”
Overload trans = “payloadSem$trans”

val _ = temp_set_mapped_fixity {fixity = Infixl 500, term_name = "pretty_app",
                                tok = "∙"};
Overload pretty_app[local] = “λf x. App Opapp [f; x]”
Overload Cif[local] = “smallStep$Cif ()”
Overload Clet[local] = “λvb. smallStep$Clet vb ()”
Overload sscont[local] = “smallStep$continue”
Overload ssret[local] = “smallStep$return”
Overload ssstep[local] = “smallStep$Estep”
Overload Capp[local] = “λop args rest. smallStep$Capp op args () rest”
Overload "❪❫"[local] = “Con NONE []”


Theorem ps2cs_11[simp]:
  ps2cs x = ps2cs y ⇔ x = y
Proof
  simp[ps2cs_def]
QED

(* ENVIRONMENT CHECK
    General check environment has something defined with property *)
Definition has_v_def:
  has_v env n cfty f =
   (∃v. nsLookup env n = SOME v
        ∧ cfty f v)
End

(* name is defined such that it cannot be easily overwritten *)
Definition in_module_def:
  in_module name =
  ∀x y (env:(modN,varN,v) namespace). nsLookup (nsBind x y env) name = nsLookup env name
End

Definition reffree_AppReturns_def:
  reffree_AppReturns P cl Q ⇔
    ∀v. P v ⇒ ∃env exp.
                do_opapp [cl;v] = SOME (env,exp) ∧
                ∀refs. ∃u.
                         eval_rel (empty_state with refs := refs) env exp
                                  (empty_state with refs := refs) u ∧
                         Q u
End

Definition reffree_Arrow_def:
  reffree_Arrow a b = λf v. ∀x. reffree_AppReturns (a x) v (b (f x))
End

val _ = set_mapped_fixity {term_name = "reffree_Arrow", tok = "~~>",
                           fixity = Infixr 750}

Theorem reffree_normal1:
  (Dm ~~> Rg) f v ⇒ (Dm --> Rg) f v
Proof
  simp[reffree_Arrow_def, reffree_AppReturns_def, Arrow_def, AppReturns_def] >>
  metis_tac[APPEND_NIL]
QED

Theorem reffree_normal2:
  (Dm1 ~~> Dm2 ~~> Rg) f v ⇒ (Dm1 --> Dm2 --> Rg) f v
Proof
  simp[reffree_Arrow_def, reffree_AppReturns_def, Arrow_def, AppReturns_def] >>
  metis_tac[APPEND_NIL]
QED

Definition at_def:
  at vs i spec f v ⇔ v = EL i vs ∧ spec f v
End

(* All constructors in conf are defined correctly and cannot be
   overwritten easily *)
Definition env_asm_def:
  env_asm env conf vs ⇔
    LENGTH vs = 8 ∧
    has_v env.c conf.nil  $= (0,TypeStamp "[]" list_type_num) ∧
    has_v env.c conf.cons $= (2,TypeStamp "::" list_type_num) ∧
    has_v env.v conf.append (at vs 0 (DATUM ~~> DATUM ~~> DATUM)) $++ ∧
    has_v env.v conf.append (at vs 0 (LIST_TYPE DATUM ~~>
                                      LIST_TYPE DATUM ~~> LIST_TYPE DATUM))$++ ∧
    has_v env.v conf.concat (at vs 1 (LIST_TYPE DATUM ~~> DATUM)) FLAT ∧
    has_v env.v conf.length (at vs 2 (DATUM ~~> NUM)) LENGTH ∧
    has_v env.v conf.null (at vs 3 (DATUM --> BOOL)) NULL ∧
    has_v env.v conf.take (at vs 4 (DATUM --> NUM --> DATUM)) (combin$C TAKE) ∧
    has_v env.v conf.drop (at vs 5 (DATUM ~~> NUM ~~> DATUM)) (combin$C DROP) ∧
    has_v env.v conf.reverse
          (at vs 6 (LIST_TYPE DATUM ~~> LIST_TYPE DATUM)) REVERSE ∧
    nsLookup env.v conf.fromList = SOME (EL 7 vs) ∧
    (∀l lv. (* fromList spec *)
       DATUM l lv ⇒
       ∃env' exp.
         do_opapp [EL 7 vs; lv] = SOME(env',exp) ∧
         ∀s1: unit semanticPrimitives$state.
           ∃ck1 ck2.
             evaluate (s1 with clock := ck1) env' [exp] =
             (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,
              Rval [Loc(LENGTH s1.refs)])) ∧
    in_module conf.append ∧
    in_module conf.concat ∧
    in_module conf.length ∧
    in_module conf.null ∧
    in_module conf.take ∧
    in_module conf.drop ∧
    in_module conf.fromList ∧
    in_module conf.reverse
End

(* LUPDATE (List Update) HELPER THEOREMS *)
Theorem LUPDATE_REPLICATE:
  ∀n m x y. n < m ⇒
   LUPDATE x n (REPLICATE m y) = REPLICATE n y ++ [x] ++ REPLICATE (m - (n + 1)) y
Proof
  Induct >> Cases >>
  rw[LUPDATE_def] >> simp[ADD1]
QED

Theorem LUPDATE_LUPDATE_c:
  ∀a b i lst rst.
    LUPDATE a i (LUPDATE b i lst) = LUPDATE a i lst
Proof
  Induct_on ‘lst’ >> Cases_on ‘i’ >>
  rw[LUPDATE_def]
QED

Theorem LUPDATE_LUPDATE:
  ∀a b i lst rst.
    LUPDATE a i (LUPDATE b i lst ++ rst) = LUPDATE a i (lst ++ rst)
Proof
  Induct_on ‘lst’ >> Cases_on ‘i’ >>
  rw[LUPDATE_def]
QED

Theorem LUPDATE_SAME':
  n < LENGTH ls ∧ EL n ls = a
  ⇒ LUPDATE a n ls = ls
Proof
  metis_tac[LUPDATE_SAME]
QED

(* FFI MANIPULATION HELPERS *)

(* Produce list of FFI events to send data *)
Definition send_events_def:
  send_events conf dest d =
  MAP (λm. IO_event "send" dest (ZIP (m,m)))(compile_message conf d)
End
(* Update FFI state based on list of FFI events *)
Definition update_state_def:
  (update_state st oracle [] = st) ∧
  (update_state st oracle (IO_event s c b::es) =
   update_state (@st'. oracle s st c (MAP FST b) = Oracle_return st' (MAP SND b))
                oracle es)
End

(* SIMPLICATIONS
   -- Written by me *)
(* -- Unnecessary FFI update *)
Theorem remove_ffi[simp]:
  ∀cSt: 'ffi semanticPrimitives$state.
    (cSt with ffi := cSt.ffi) = cSt
Proof
  simp[state_component_equality]
QED
(* -- Unnecessary memory update *)
Theorem remove_refs[simp]:
  ∀cSt: 'ffi semanticPrimitives$state.
    (cSt with refs := cSt.refs) = cSt
Proof
  simp[state_component_equality]
QED
(* -- Unnecessary conversion to string then back *)
Theorem undo_encode_decode[simp]:
  ∀MEP:word8 list.
    MAP (λc. n2w (ORD c)) (EXPLODE (MAP (CHR ∘ w2n) MEP)) = MEP
Proof
  rw[] >> Induct_on ‘MEP’ >> rw[MAP,EXPLODE_def] >>
  ‘n2w o ORD o CHR o w2n = I’
    suffices_by metis_tac[o_DEF,I_THM] >>
  simp[n2w_ORD_CHR_w2n]
QED

Definition result_bind_def[simp]:
  result_bind (x, Rval v) f = f (x,v) ∧
  result_bind (x, Rerr e) f = (x, Rerr e)
End

Definition result_return_def:
  result_return (x,v) = (x, Rval v)
End

val _ = declare_monad("result", {bind = “result_bind”, ignorebind = NONE,
                                 unit = “result_return”, fail = NONE,
                                 choice = NONE, guard = NONE})

val _ = enable_monad "result"

Theorem bind_assoc[simp]:
  result_bind (result_bind m f) g =
  result_bind m (combin$C (result_bind o f) g)
Proof
  Cases_on ‘m’ >> Cases_on ‘r’ >> simp[]
QED

Theorem generic_casebind[simp]:
  (case x of (s, Rval v) => f s v | (s, Rerr e) => (s, Rerr e)) =
  do (s,v) <- x ; f s v od
Proof
  Cases_on ‘x’ >> Cases_on ‘r’ >> simp[]
QED

val _ = augment_srw_ss [rewrites [o_UNCURRY_R, o_ABS_R, C_UNCURRY_L, C_ABS_L]]

Theorem bind_eq_Rval:
  result_bind x f = (s, Rval rvs) ⇔
  ∃s0 rvs0. x = (s0,Rval rvs0) ∧ f (s0, rvs0) = (s, Rval rvs)
Proof
  Cases_on ‘x’ >> Cases_on ‘r’ >> simp[]
QED

Definition check_option_def[simp]:
  check_option NONE e (s:α state) = (s, Rerr e) ∧
  check_option (SOME y) e s = (s, Rval y)
End

Theorem option_bind:
  (case x of NONE => (s, Rerr e) | SOME y => f s y) =
  do (s,y) <- check_option x e s ; f s y od
Proof
  Cases_on ‘x’ >> simp[]
QED

Overload TRUE[local] = “Conv (SOME (TypeStamp "True" bool_type_num)) []”
Overload FALSE[local] = “Conv (SOME (TypeStamp "False" bool_type_num)) []”;

Overload ";;"[local] = “Let NONE”
val _ = temp_set_fixity ";;" (Infixr 501)

Overload "𝕍"[local] = “λn. Var (Short n)”;

Overload Pretty_Aw8update[local] = “λa i v. App Aw8update [a;i;v]”;
val _ = temp_add_rule {
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
  fixity = Infixl 600,
  paren_style = OnlyIfNecessary,
  pp_elements = [PPBlock([TOK "⟦", BreakSpace(0,2),
                          PPBlock([TM], (PP.INCONSISTENT,0)),
                          BreakSpace(0,0),
                          TOK "⟧"], (PP.CONSISTENT,0)),
                 HardSpace 1,
                 TOK "↜", BreakSpace(1,2)],
  term_name = "Pretty_Aw8update"}
Overload CN[local] = “λn. Lit (IntLit n)”
Overload CW[local] = “λn. Lit (Word8 n)”
Overload "-"[local] = “λm n. App (Opn Minus) [m;n]”
Overload "+"[local] = “λm n. App (Opn Plus) [m;n]”
Overload a8len[local] = “λe. App Aw8length [e]”

Theorem nsOptBind_NONE[simp]:
  nsOptBind NONE x env = env
Proof
  simp[nsOptBind_def]
QED

Theorem nsOptBind_SOME[simp]:
  nsOptBind (SOME v) x env = nsBind v x env
Proof
  simp[nsOptBind_def]
QED

Theorem evaluate_letNONE:
  evaluate st env [Let NONE e1 e2] =
     do
        (st,v) <- evaluate st env [e1] ;
        evaluate st env [e2]
     od
Proof
  simp[evaluate_def] >> Cases_on‘evaluate st env [e1]’ >>
  rename [‘evaluate _ _ _ = (v, res)’] >> Cases_on ‘res’ >> simp[]
QED
Theorem evaluate_nonsing[simp] = cj 2 evaluate_def
Theorem evaluate_opapp[simp]:
  evaluate st env [App Opapp [e1; e2]] =
   do
     (st1,vs2) <- evaluate st env [e2];
     (st2,vs1) <- evaluate st1 env [e1];
     case do_opapp (REVERSE (HD vs2::vs1)) of
       NONE => (st2, Rerr (Rabort Rtype_error))
     | SOME (env, e) => if st2.clock = 0 then (st2,Rerr (Rabort Rtimeout_error))
                        else evaluate (dec_clock st2) env [e]
   od
Proof
  simp[evaluate_def] >>
  Cases_on ‘evaluate st env [e2]’ >>
  rename [‘evaluate st env [e2] = (st1, res2)’] >>
  Cases_on ‘res2’ >> simp[] >>
  ‘(∃st2 vs1. evaluate st1 env [e1] = (st2, Rval vs1)) ∨
   ∃st2 e. evaluate st1 env [e1] = (st2, Rerr e)’
     by metis_tac[pair_CASES, TypeBase.nchotomy_of “:(α,β) result”] >>
  simp[]
QED

val evalths = evaluate_def |> CONJUNCTS
fun find_evalform q =
  let
    val e = Parse.typed_parse_in_context “:ast$exp” [] q
    val l = listSyntax.mk_list([e], type_of e)
    fun test th =
      let val (_, eqn) = strip_forall (concl th)
      in
          can (match_term l) (rand (lhs eqn))
      end

  in
    valOf (List.find test evalths) handle Option => failwith "no match"
  end

Theorem evaluate_lit[simp] = find_evalform ‘Lit _’
Theorem evaluate_var[simp] = find_evalform ‘Var _’

val _ = print "do_app_thm calculation: "
val do_app_thm =
  let
    fun thry kid =
        case TypeBase.read kid of
          NONE => NONE
        | SOME tyi => SOME {case_const = TypeBasePure.case_const_of tyi,
                            constructors = TypeBasePure.constructors_of tyi}
    val def_t = do_app_def |> concl |> strip_forall |> #2
    val (_, cases0) =  def_t |> rhs |> Pmatch.strip_case thry
    val cases = map (fn (pat, _) => dest_pair pat) cases0
    val (op_t, vs_t) = case strip_comb (lhs def_t) of
                         (_, [_, t1, t2]) => (t1, t2)
                       | _ => raise Fail "foo"
    fun do1_0 (inop, invs) = do_app_def |> SPEC_ALL
                                        |> INST [op_t |-> inop, vs_t |-> invs]
                                        |> SRULE []
    fun doi n x = (TextIO.print (Int.toString n ^ " "); do1_0 x)
  in
    LIST_CONJ (mapi doi cases) before print "- done \n"
  end

(* SENDLOOP CORRECTNESS *)

Theorem evaluate_choose_final_clock:
  (∀(s0:α state) env es s res ck.
     evaluate s0 env es = (s,res) ∧ ck ≤ s.clock ⇒
     evaluate (s0 with clock := s0.clock + ck - s.clock) env es =
     (s with clock := ck, res)) ∧
  (∀(s0:α state) (env:v sem_env) (v1:v) (ms:(pat#exp)list) (v2:v) s res ck.
     evaluate_match s0 env v1 ms v2 = (s,res) ∧ ck ≤ s.clock ⇒
     evaluate_match (s0 with clock := s0.clock + ck - s.clock) env v1 ms v2 =
     (s with clock := ck, res))
Proof
  ho_match_mp_tac evaluate_ind >> rpt strip_tac
  >- (* nil *) gs[]
  >- ((* cons *) simp[] >>
      qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac >> simp[] >>
      Cases_on ‘evaluate s0 env [e1]’ >> gs[] >>
      rename [‘evaluate _ _ [_] = (s00,res00)’] >> Cases_on ‘res00’ >> gs[]
      >- (Cases_on ‘evaluate s00 env (e2::es)’ >>
          rename1 ‘evaluate s00 env (e2::es) = (s01,r01)’ >>
          Cases_on ‘r01’ >> gs[] >>
          qabbrev_tac ‘d2 = s00.clock - s01.clock’ >>
          qabbrev_tac ‘d1 = s0.clock - s00.clock’ >>
          ‘s01.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
          rw[] >> rename [‘s01.clock ≤ s00.clock’] >>
          ‘ck + d2 ≤ s00.clock’ by simp[Abbr‘d2’] >>
          first_x_assum drule >> simp[Abbr‘d2’]) >>
      rw[] >> gs[])
  >- ((* lit *) gs[])
  >- ((* raise *) gs[find_evalform ‘Raise _’] >>
      rename [‘evaluate s0 env [e] = _’] >> rw[] >>
      Cases_on ‘evaluate s0 env [e]’ >>
      rename [‘evaluate s0 env [e] = (s,r0)’] >>
      Cases_on ‘r0’ >> gvs[])
  >- ((* handle *)
      gvs[find_evalform ‘Handle _ _’, AllCaseEqs()] >>
      rename [‘evaluate s0 env [e] = (s00,Rerr (Rraise exn))’,
              ‘evaluate_match s00 _ _ _ _ = (s, res)’] >>
      qabbrev_tac ‘d2 = s00.clock - s.clock’ >>
      qabbrev_tac ‘d1 = s0.clock - s00.clock’ >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      ‘ck + d2 ≤ s00.clock’ by simp[Abbr‘d2’] >>
      first_x_assum drule >> simp[Abbr‘d2’])
  >- ((* Con *) gs[find_evalform ‘Con _ _’, AllCaseEqs()] >>
      rename [‘evaluate s0 env (REVERSE es) = _’] >>
      Cases_on ‘evaluate s0 env (REVERSE es)’ >> gvs[] >>
      rename [‘evaluate s0 env (REVERSE es) = (s',res')’] >>
      Cases_on ‘res'’ >> gvs[AllCaseEqs()])
  >- (* Var *) gs[AllCaseEqs()]
  >- (* Fun *) gs[AllCaseEqs(), find_evalform ‘Fun _ _’]
  >- ((* App *) gvs[AllCaseEqs(), find_evalform ‘App _ _’] >>
      rename [‘evaluate s0 env (REVERSE es) = _’] >>
      Cases_on ‘evaluate s0 env (REVERSE es)’ >>
      rename [‘evaluate s0 env (REVERSE es) = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs(), dec_clock_def] >>
      qabbrev_tac ‘d2 = s00.clock - 1 - s.clock’ >>
      ‘(s00 with clock := s00.clock - 1).clock = s00.clock - 1’ by simp[] >>
      ‘s.clock ≤ s00.clock - 1’ by metis_tac[evaluate_clock] >>
      ‘s00.clock = s.clock + d2 + 1’ by simp[Abbr‘d2’] >> gs[] >>
      first_x_assum (qspec_then ‘ck + d2 + 1’ mp_tac) >> simp[])
  >- ((* Log *) gvs[AllCaseEqs(), find_evalform ‘Log _ _ _’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* If *) gvs[AllCaseEqs(), find_evalform ‘If _ _ _ ’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* Mat *) gvs[AllCaseEqs(), find_evalform ‘Mat _ _ ’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* Let *) gvs[AllCaseEqs(), find_evalform ‘Let _ _ _’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* Letrec *) gvs[AllCaseEqs(), find_evalform ‘Letrec _ _ ’])
  >- ((* Tannot *) gvs[AllCaseEqs(), find_evalform ‘Tannot _ _ ’])
  >- ((* Lannot *) gvs[AllCaseEqs(), find_evalform ‘Lannot _ _ ’])
  >- ((* match [] *) gs[evaluate_def]) >>
  (* match (cons) *)
  gvs[evaluate_def,AllCaseEqs()]
QED

Theorem evaluate_choose_final_clock':
  (∀(s0:α state) env es s res ck.
     evaluate s0 env es = (s,res) ∧ res ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate (s0 with clock := s0.clock + ck - s.clock) env es =
     (s with clock := ck, res)) ∧
  (∀(s0:α state) (env:v sem_env) (v1:v) (ms:(pat#exp)list) (v2:v) s res ck.
     evaluate_match s0 env v1 ms v2 = (s,res) ∧
     res ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate_match (s0 with clock := s0.clock + ck - s.clock) env v1 ms v2 =
     (s with clock := ck, res))
Proof
  ho_match_mp_tac evaluate_ind >> rpt strip_tac
  >- (* nil *) gs[]
  >- ((* cons *) simp[] >>
      qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac >> simp[] >>
      Cases_on ‘evaluate s0 env [e1]’ >> gs[] >>
      rename [‘evaluate _ _ [_] = (s00,res00)’] >> Cases_on ‘res00’ >> gs[]
      >- (Cases_on ‘evaluate s00 env (e2::es)’ >>
          rename1 ‘evaluate s00 env (e2::es) = (s01,r01)’ >>
          Cases_on ‘r01’ >> gs[] >>
          qabbrev_tac ‘d2 = s00.clock - s01.clock’ >>
          qabbrev_tac ‘d1 = s0.clock - s00.clock’ >>
          ‘s01.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
          rw[] >> rename [‘s01.clock ≤ s00.clock’] >>
          first_x_assum (qspec_then ‘ck + d2’ mp_tac) >> simp[Abbr‘d2’]) >>
      rw[] >> gs[])
  >- ((* lit *) gs[])
  >- ((* raise *) gs[find_evalform ‘Raise _’] >>
      rename [‘evaluate s0 env [e] = _’] >> rw[] >>
      Cases_on ‘evaluate s0 env [e]’ >>
      rename [‘evaluate s0 env [e] = (s,r0)’] >>
      Cases_on ‘r0’ >> gvs[])
  >- ((* handle *)
      gvs[find_evalform ‘Handle _ _’, AllCaseEqs()] >>
      rename [‘evaluate s0 env [e] = (s00,Rerr (Rraise exn))’,
              ‘evaluate_match s00 _ _ _ _ = (s, res)’] >>
      qabbrev_tac ‘d2 = s00.clock - s.clock’ >>
      qabbrev_tac ‘d1 = s0.clock - s00.clock’ >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum $ qspec_then ‘ck + d2’ mp_tac >> simp[Abbr‘d2’])
  >- ((* Con *) gs[find_evalform ‘Con _ _’, AllCaseEqs()] >>
      rename [‘evaluate s0 env (REVERSE es) = _’] >>
      Cases_on ‘evaluate s0 env (REVERSE es)’ >> gvs[] >>
      rename [‘evaluate s0 env (REVERSE es) = (s',res')’] >>
      Cases_on ‘res'’ >> gvs[AllCaseEqs()])
  >- (* Var *) gs[AllCaseEqs()]
  >- (* Fun *) gs[AllCaseEqs(), find_evalform ‘Fun _ _’]
  >- ((* App *) gvs[AllCaseEqs(), find_evalform ‘App _ _’] >>
      rename [‘evaluate s0 env (REVERSE es) = _’] >>
      Cases_on ‘evaluate s0 env (REVERSE es)’ >>
      rename [‘evaluate s0 env (REVERSE es) = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs(), dec_clock_def] >>
      qabbrev_tac ‘d2 = s00.clock - 1 - s.clock’ >>
      ‘(s00 with clock := s00.clock - 1).clock = s00.clock - 1’ by simp[] >>
      ‘s.clock ≤ s00.clock - 1’ by metis_tac[evaluate_clock] >>
      ‘s00.clock = s.clock + d2 + 1’ by simp[Abbr‘d2’] >> gs[] >>
      first_x_assum (qspec_then ‘ck + d2 + 1’ mp_tac) >> simp[])
  >- ((* Log *) gvs[AllCaseEqs(), find_evalform ‘Log _ _ _’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* If *) gvs[AllCaseEqs(), find_evalform ‘If _ _ _ ’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* Mat *) gvs[AllCaseEqs(), find_evalform ‘Mat _ _ ’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* Let *) gvs[AllCaseEqs(), find_evalform ‘Let _ _ _’] >>
      rename [‘evaluate s0 env [e1] = _’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s00,res00)’] >>
      Cases_on ‘res00’ >> gvs[AllCaseEqs()] >>
      ‘s.clock ≤ s00.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum (qspec_then ‘ck + (s00.clock - s.clock)’ mp_tac) >>
      simp[])
  >- ((* Letrec *) gvs[AllCaseEqs(), find_evalform ‘Letrec _ _ ’])
  >- ((* Tannot *) gvs[AllCaseEqs(), find_evalform ‘Tannot _ _ ’])
  >- ((* Lannot *) gvs[AllCaseEqs(), find_evalform ‘Lannot _ _ ’])
  >- ((* match [] *) gs[evaluate_def]) >>
  (* match (cons) *)
  gvs[evaluate_def,AllCaseEqs()]
QED

Theorem evaluate_induce_timeout:
  (∀(s0:α state) env es s res ck.
     evaluate s0 env es = (s,res) ∧ res ≠ Rerr (Rabort Rtimeout_error) ⇒
     (ck < s0.clock - s.clock ⇔
        ∃s'. evaluate (s0 with clock := ck) env es =
             (s', Rerr (Rabort Rtimeout_error))) ∧
     (s0.clock - s.clock ≤ ck ⇔
        evaluate (s0 with clock := ck) env es =
        (s with clock := ck + s.clock - s0.clock, res))) ∧
  (∀(s0:α state) (env:v sem_env) (v1:v) (ms:(pat#exp)list) (v2:v) s res ck.
     evaluate_match s0 env v1 ms v2 = (s,res) ∧
     res ≠ Rerr (Rabort Rtimeout_error) ⇒
     (ck < s0.clock - s.clock ⇔
        ∃s'.
          evaluate_match (s0 with clock := ck) env v1 ms v2 =
          (s', Rerr (Rabort Rtimeout_error))) ∧
     (s0.clock - s.clock ≤ ck ⇔
        evaluate_match (s0 with clock := ck) env v1 ms v2 =
        (s with clock := ck + s.clock - s0.clock, res)))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- (* nil *) simp[]
  >- ((* cons *) simp[] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e1]’] >> Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s1, res)’] >>
      reverse (Cases_on ‘res’ >> simp[])
      >- (strip_tac >> gvs[] >> first_x_assum $ qspec_then ‘ck’ mp_tac >>
          rename [‘evaluate s0 env [e1] = (s,Rerr e)’] >>
          Cases_on ‘ck < s0.clock - s.clock’ >> simp[PULL_EXISTS]) >>
      gs[] >>
      ‘s1.clock ≤ s0.clock’ by metis_tac[evaluate_clock] >>
      first_x_assum $ qspec_then ‘ck’ mp_tac >>
      Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS]
      >- (rename [‘evaluate s0 env [e1] = (s1,Rval v)’,
                  ‘evaluate s1 env (e2::es)’] >>
          Cases_on ‘evaluate s1 env (e2::es)’ >> simp[] >>
          rename [‘evaluate s1 env (e2::es) = (s2,res)’] >> Cases_on ‘res’ >>
          simp[] >> ntac 3 strip_tac >> gvs[] >>
          rpt (dxrule_then assume_tac (cj 1 evaluate_clock)) >> simp[]) >>
      strip_tac >> gvs[] >>
      qpat_x_assum ‘evaluate (s0 with clock := ck) _ _ = _ ’ kall_tac >>
      rename1 ‘evaluate s1 env (e2::es)’ >>
      Cases_on ‘evaluate s1 env (e2::es)’ >>
      rename1‘ evaluate s1 env (e2::es) = (s2,res2)’ >>
      Cases_on ‘res2’ >> gvs[] >> strip_tac >> gvs[] >>
      qabbrev_tac ‘ck1 = ck + s1.clock - s0.clock’ >>
      first_x_assum $ qspec_then ‘ck1’ mp_tac >>
      Cases_on ‘ck1 < s1.clock - s.clock’ >> simp[PULL_EXISTS]
      >- (drule (cj 1 evaluate_clock) >> simp[Abbr‘ck1’]) >>
      rw[Abbr‘ck1’])
  >- (* Lit *) simp[]
  >- ((* Raise *) simp[find_evalform ‘Raise _’] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e]’] >>
      Cases_on ‘evaluate s0 env [e]’ >>
      rename [‘evaluate s0 env [e] = (s1, res)’] >>
      Cases_on ‘res’ >> simp[] >> strip_tac >> gvs[] >>
      drule_then assume_tac (cj 1 evaluate_clock) >>
      first_x_assum $ qspec_then ‘ck’ mp_tac >>
      Cases_on ‘ck < s0.clock - s.clock’ >> simp[PULL_EXISTS])
  >- ((* handle *)
      simp[find_evalform ‘Handle _ _ ’, AllCaseEqs(), PULL_EXISTS] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e] = (s1, res)’] >>
      Cases_on ‘res’ >> gvs[] >> strip_tac >> gvs[]
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          rename [‘evaluate s0 env [e] = (s1,Rval v)’] >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS])
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          drule_then assume_tac (cj 2 evaluate_clock) >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS] >>
          strip_tac >> qabbrev_tac ‘ck1 = ck + s1.clock - s0.clock’ >>
          first_x_assum $ qspec_then ‘ck1’ mp_tac >>
          Cases_on ‘ck1 < s1.clock - s.clock’ >> simp[PULL_EXISTS, Abbr‘ck1’])
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          rename [‘evaluate s0 env [e] = (s1,Rerr (Rraise exn))’] >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS]) >>
      drule_then assume_tac (cj 1 evaluate_clock) >>
      first_x_assum $ qspec_then ‘ck’ mp_tac >>
      rename [‘evaluate s0 env [e] = (s1,Rerr (Rabort abt))’] >>
      Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS])
  >- ((* Con *) simp[find_evalform ‘Con _ _’, AllCaseEqs()] >> rpt gen_tac >>
      strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      rename [‘evaluate s0 env (REVERSE es) = _ ’] >>
      Cases_on ‘evaluate s0 env (REVERSE es)’ >> gvs[] >>
      rename [‘evaluate s0 env (REVERSE es) = (s1,res0) ’] >> Cases_on ‘res0’ >>
      gvs[] >> rename [‘evaluate s0 env (REVERSE es) = (s1,_) ’] >>
      drule_then assume_tac (cj 1 evaluate_clock) >>
      first_x_assum $ qspec_then ‘ck’ mp_tac >>
      Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS] >>
      gvs[AllCaseEqs()])
  >- ((* Var *) simp[AllCaseEqs()] >> rw[] >> simp[])
  >- ((* Fun *) simp[find_evalform ‘Fun _ _’])
  >- ((* App *) simp[find_evalform ‘App _ _’] >> rpt gen_tac >> strip_tac >>
      rpt gen_tac  >>
      rename [‘evaluate s0 env (REVERSE es) = _ ’] >>
      Cases_on ‘evaluate s0 env (REVERSE es)’ >> gvs[] >>
      rename [‘evaluate s0 env (REVERSE es) = (s1,res0) ’] >> Cases_on ‘res0’ >>
      gvs[] >> rename [‘evaluate s0 env (REVERSE es) = (s1,_) ’]
      >- (reverse (Cases_on ‘op = Opapp’) >> simp[] >>
          drule_then assume_tac (cj 1 evaluate_clock) >>
          strip_tac
          >- (first_x_assum $ qspec_then ‘ck’ mp_tac >>
              Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS] >>
              gvs[AllCaseEqs()]) >>
          gvs[AllCaseEqs()]
          >- (first_x_assum $ qspec_then ‘ck’ mp_tac >>
              rename [‘evaluate s0 env (REVERSE es) = (s1,_)’] >>
              Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS] >>
              gvs[AllCaseEqs()]) >>
          gvs[dec_clock_def] >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          rename [‘evaluate s0 env (REVERSE es) = (s1,_)’] >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS] >>
          gvs[AllCaseEqs()]
          >- (drule_then assume_tac (cj 1 evaluate_clock) >> gs[]) >>
          drule_then assume_tac (cj 1 evaluate_clock) >> gs[] >>
          strip_tac >>
          qabbrev_tac ‘ck1 = ck + s1.clock - s0.clock’ >>
          first_x_assum $ qspec_then ‘ck1 - 1’ mp_tac >>
          Cases_on ‘ck1 - 1 < s1.clock - (s.clock + 1)’ >>
          simp[PULL_EXISTS, Abbr‘ck1’] >> dsimp[]) >>
      strip_tac >> gvs[] >> drule_then assume_tac (cj 1 evaluate_clock) >>
      rename [‘s1.clock ≤ s0.clock’] >> first_x_assum $ qspec_then ‘ck’ mp_tac>>
      Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS])
  >- ((* Log *) simp[find_evalform ‘Log _ _ _’, AllCaseEqs()] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e1] = (_, Rval _)’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s1, res)’] >>
      reverse (Cases_on ‘res’ >> gs[AllCaseEqs()])
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          strip_tac >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS]) >>
      strip_tac >> gvs[]
      >- (rename [‘evaluate s0 env [e1] = (s1, Rval v)’,
                  ‘do_log _ _ _ = NONE’]>>
          drule_then assume_tac (cj 1 evaluate_clock) >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS])
      >- (rename [‘evaluate s0 env [e1] = (s1, Rval v)’,
                  ‘evaluate s1 env [e2] = (s, _)’]>>
          ‘s.clock ≤ s1.clock ∧ s1.clock ≤ s0.clock’
            by metis_tac[evaluate_clock] >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >>simp[PULL_EXISTS] >>
          first_x_assum $ qspec_then ‘ck + s1.clock - s0.clock’ mp_tac >>
          Cases_on ‘ck + s1.clock - s0.clock < s1.clock - s.clock’ >>
          simp[PULL_EXISTS])
      >- (rename [‘evaluate s0 env [e1] = (s1, Rval v)’,
                  ‘do_log _ _ _ = SOME (Val v')’]>>
          drule_then assume_tac (cj 1 evaluate_clock) >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> simp[PULL_EXISTS]))
  >- ((* If *) simp[find_evalform ‘If _ _ _’, AllCaseEqs()] >> rpt gen_tac >>
      strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e1] = (_, Rval _)’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s1, res)’] >>
      reverse (Cases_on ‘res’ >> gs[AllCaseEqs()])
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          strip_tac >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS]) >>
      drule_then assume_tac (cj 1 evaluate_clock) >> strip_tac
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          strip_tac >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS]) >>
      drule_then assume_tac (cj 1 evaluate_clock) >>
      first_x_assum $ qspec_then ‘ck’ mp_tac >>
      Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS] >> strip_tac >>
      rename [‘s.clock ≤ s1.clock’, ‘s1.clock ≤ s0.clock’] >>
      first_x_assum $ qspec_then ‘ck + s1.clock - s0.clock’ mp_tac >>
      Cases_on‘ck + s1.clock - s0.clock < s1.clock - s.clock’ >>
      gvs[PULL_EXISTS])
  >- ((* Mat *) simp[find_evalform ‘Mat _ _’, AllCaseEqs()] >>
      rpt gen_tac >>
      strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e1] = (_, Rval _)’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s1, res)’] >>
      reverse (Cases_on ‘res’ >> gs[AllCaseEqs()])
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          strip_tac >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS]) >>
      reverse strip_tac
      >- (drule_then assume_tac (cj 1 evaluate_clock) >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS]) >>
      drule_then assume_tac (cj 1 evaluate_clock) >>
      drule_then assume_tac (cj 2 evaluate_clock) >>
      first_x_assum $ qspec_then ‘ck’ mp_tac >>
      Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS] >> strip_tac >>
      rename [‘s.clock ≤ s1.clock’, ‘s1.clock ≤ s0.clock’] >>
      first_x_assum $ qspec_then ‘ck + s1.clock - s0.clock’ mp_tac >>
      Cases_on‘ck + s1.clock - s0.clock < s1.clock - s.clock’ >>
      gvs[PULL_EXISTS])
  >- ((* Let *) simp [find_evalform ‘Let _ _ _’, AllCaseEqs()] >>
      rpt gen_tac >>
      strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e1] = (_, Rval _)’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s1, res)’] >>
      reverse (Cases_on ‘res’ >> gs[AllCaseEqs()]) >>
      drule_then assume_tac (cj 1 evaluate_clock)
      >- (strip_tac >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS]) >>
      drule_then assume_tac (cj 1 evaluate_clock) >> strip_tac >>
      drule_then assume_tac (cj 1 evaluate_clock) >>
      first_x_assum $ qspec_then ‘ck’ mp_tac >>
      Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS] >> strip_tac >>
      rename [‘s.clock ≤ s1.clock’, ‘s1.clock ≤ s0.clock’] >>
      first_x_assum $ qspec_then ‘ck + s1.clock - s0.clock’ mp_tac >>
      Cases_on‘ck + s1.clock - s0.clock < s1.clock - s.clock’ >>
      gvs[PULL_EXISTS])
  >- ((* Letrec *) simp[find_evalform ‘Letrec _ _’, AllCaseEqs()] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      rename [‘evaluate s0 env [e1] = (_, _)’] >>
      Cases_on ‘evaluate s0 env [e1]’ >>
      rename [‘evaluate s0 env [e1] = (s1, res)’] >>
      reverse (Cases_on ‘res’ >> gs[AllCaseEqs()]) >>
      drule_then assume_tac (cj 1 evaluate_clock)
      >- (strip_tac >> gs[] >>
          first_x_assum $ qspec_then ‘ck’ mp_tac >>
          Cases_on ‘ck < s0.clock - s1.clock’ >> gvs[PULL_EXISTS]) >>
      reverse strip_tac >> simp[] >> gs[])
  >- ((* Tannot *) simp[find_evalform ‘Tannot _ _’, AllCaseEqs()])
  >- ((* Lannot *) simp[find_evalform ‘Lannot _ _’, AllCaseEqs()])
  >- ((* match [] *) simp[evaluate_def]) >>
  (* match cons *) simp[evaluate_def,AllCaseEqs()] >> rpt gen_tac  >>
  strip_tac >> rpt gen_tac >>
  rename [‘evaluate_match s0 env v1 ms v2 = (s1, res)’] >>
  reverse (Cases_on ‘res’ >> gs[AllCaseEqs()]) >> strip_tac >> gs[]
QED

Theorem evaluate_generalise':
  ∀env exp ck1 ck2 refs refs' u.
      evaluate (empty_state with <|clock := ck1; refs := refs|>) env [exp] =
      (empty_state with <|clock := ck2; refs := refs'|>, Rval [u])
      ⇒
      ∀st : 'a semanticPrimitives$state s nc1 vs.
        evaluate (st with <| clock := nc1; refs := refs|>) env [exp] =
        (s, Rval vs) ⇔
          s = st with <| clock := nc1 + ck2 - ck1; refs := refs' |> ∧
          vs = [u] ∧ ck1 - ck2 ≤ nc1
Proof
  rpt strip_tac >>
  drule_then assume_tac (cj 1 evaluate_clock) >> gs[] >>
  dxrule (evaluate_ffi_intro |> cj 1
           |> INST_TYPE [beta |-> alpha, alpha |-> “:unit”]) >> simp[] >>
  strip_tac >>
  pop_assum (C(resolve_then (Pos hd) mp_tac)
             (cj 1 evaluate_choose_final_clock')) >> simp[] >>
  strip_tac >> reverse eq_tac >> strip_tac
  >- (first_x_assum $
        qspecl_then [‘st with <| clock := ck1; refs := refs|>’,
                     ‘ck2 + nc1 - ck1’] mp_tac >>
      simp[]) >>
  drule_then assume_tac (cj 1 evaluate_clock) >> gs[] >>
  first_x_assum $
    qspecl_then [‘st with <| clock := ck1; refs := refs|>’,
                 ‘ck2’] mp_tac >> simp[] >> strip_tac >>
  drule (cj 1 evaluate_induce_timeout) >> simp[] >>
  disch_then $ qspec_then ‘nc1’ mp_tac >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem AppReturns_thm:
  AppReturns P cl Q ⇔
    ∀v. P v ⇒
        ∃env exp.
          do_opapp [cl;v] = SOME (env,exp) ∧
          ∀refs.
            ∃refs' u.
              eval_rel (empty_state with refs := refs) env exp
                       (empty_state with refs := refs++refs') u ∧
              Q u
Proof
  fs [AppReturns_def] \\ eq_tac \\ rw []
  \\ first_x_assum drule
  \\ Cases_on ‘cl’ \\ fs [do_opapp_def,AllCaseEqs()]
  \\ rename [‘find_recfun x1 x2’]
  \\ Cases_on ‘find_recfun x1 x2’ \\ fs []
  \\ PairCases_on ‘x’ \\ fs []
  \\ rename [‘ALL_DISTINCT xx’]
  \\ Cases_on ‘ALL_DISTINCT xx’ \\ fs []
QED

Theorem eval_rel0_thm:
  eval_rel s1 env e s2 v ⇔ s1.clock = s2.clock ∧
                           ∃dc. evaluate (s1 with clock := dc) env [e] =
                                (s2 with clock := 0, Rval [v])
Proof
  simp[eval_rel_def, EQ_IMP_THM] >> reverse (rpt strip_tac)
  >- metis_tac[] >>
  drule (cj 1 evaluate_induce_timeout) >> simp[] >>
  disch_then $ qspec_then ‘ck1 - ck2’ mp_tac >> simp[] >>
  drule_then assume_tac (cj 1 evaluate_clock) >> fs[] >>
  simp[] >> metis_tac[]
QED

Theorem evaluate_ffi_intro' =
  evaluate_ffi_intro  |> cj 1
     |> SRULE [GSYM RIGHT_FORALL_IMP_THM]
     |> CONV_RULE (pull_namedallvar_conv "t")
     |> Q.SPECL [‘t with <| clock := s.clock; refs := s.refs|>’, ‘s’]
     |> SRULE []
     |> Q.GENL [‘t’, ‘s’]

Theorem clock_selfrefs[simp,local]:
  s with <| clock := ck; refs := s.refs |> = s with <| clock := ck |>
Proof
  simp[state_component_equality]
QED


val _ = augment_srw_ss [SatisfySimps.SATISFY_ss]
Theorem padv_correct':
  DATUM l lv ⇒
  ∀(s:plffi semanticPrimitives$state).
    ∃refs ck1 ck2 n.
      ∀env.
        env_asm env conf vs ⇒
        ∃clv e env'.
          evaluate (s with clock:= ck1) env [padv conf] =
            (s with clock := ck1, Rval [clv]) ∧
          do_opapp [clv; lv] = SOME (env',e) ∧
          evaluate (s with clock:= ck1) env' [e] =
            (s with <|clock := ck2; refs := s.refs ++ refs|>,
             Rval [Loc n]) ∧
          store_lookup n (s.refs ++ refs) = SOME (W8array (pad conf l))
Proof
  rpt strip_tac >>
  ‘∃lenf.
     ∀env. env_asm env conf vs ⇒
           ∀yv.
             nsLookup (nsBind "y" yv (nsBind "x" lv env.v)) conf.length =
             SOME lenf ∧ (DATUM ~~> NUM) LENGTH lenf’
    by (simp[env_asm_def, in_module_def, has_v_def, PULL_EXISTS, at_def] >>
        qexists_tac ‘EL 2 vs’ >> simp[]) >>
  gs[reffree_Arrow_def, reffree_AppReturns_def, FORALL_AND_THM, IMP_CONJ_THM] >>
  first_x_assum (drule_at_then (Pos (el 2)) assume_tac) >>
  RULE_ASSUM_TAC (SRULE [LEFT_FORALL_IMP_THM]) >>
  RULE_ASSUM_TAC
    (SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM,
                           FORALL_AND_THM, IMP_CONJ_THM]) >>
  pop_assum (qx_choosel_then [‘lencl’, ‘lenexp’]
             $ CONJUNCTS_THEN2 assume_tac
               (qx_choose_then ‘lenvalf’ strip_assume_tac)) >>
  gs[NUM_def, INT_def] >> (* lenvalf now unused *) pop_assum kall_tac >>
  gs[eval_rel0_thm] >>
  RULE_ASSUM_TAC
    (SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM,
                           FORALL_AND_THM, IMP_CONJ_THM]) >>
  pop_assum (qx_choosel_then [‘lenclkf’] assume_tac) >>
  pop_assum (C (resolve_then (Pos hd) assume_tac)
             (INST_TYPE [alpha |-> “:plffi”] evaluate_generalise')) >>
  qabbrev_tac
    ‘LENCLK = λ(s:plffi state).
              lenclkf (s.refs ++
                       [W8array (REPLICATE (conf.payload_size + 1) 0w)])’ >>
  simp[find_evalform ‘Fun _ _’, padv_def, do_opapp_def] >>
  simp[find_evalform ‘Let _ _ _’, bind_eq_Rval, PULL_EXISTS] >>
  simp[find_evalform ‘App _ _’, buffer_size_def, do_app_thm, store_alloc_def] >>
  simp[find_evalform ‘If _ _ _’, bind_eq_Rval, AllCaseEqs(), PULL_EXISTS] >>
  simp[find_evalform ‘App _ _’, payload_size_def, bind_eq_Rval,
       AllCaseEqs(), PULL_EXISTS, dec_clock_def] >>
  CONV_TAC (pull_namedexvar_conv "ck1") >>
  Q.REFINE_EXISTS_TAC ‘LENCLK s + clk1 + 1’ >>
  simp[do_app_thm, terminationTheory.do_eq_def, lit_same_type_def, do_if_def]>>
  ‘∃takef.
     ∀env. env_asm env conf vs ⇒
           ∀yv.
             nsLookup (nsBind "y" yv (nsBind "x" lv env.v)) conf.take =
             SOME takef ∧ (DATUM --> NUM --> DATUM) (flip TAKE) takef’
    by (simp[env_asm_def, in_module_def, has_v_def, PULL_EXISTS, at_def] >>
        qexists_tac ‘EL 4 vs’ >> simp[]) >>
  RULE_ASSUM_TAC
    (SRULE [FORALL_AND_THM, IMP_CONJ_THM]) >>
  fs[LEFT_FORALL_IMP_THM] >>
  gs[Once Arrow_def, AppReturns_thm] >>
  pop_assum (drule_at_then (Pos (el 2)) assume_tac) >>
  RULE_ASSUM_TAC
    (SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM,
                           FORALL_AND_THM, IMP_CONJ_THM]) >>
  pop_assum (qx_choosel_then [‘tkclv’, ‘tkenv’] $
             CONJUNCTS_THEN2 assume_tac
             (qx_choosel_then [‘tkreff’, ‘tkvalf’]
              strip_assume_tac)) >>
  Cases_on ‘LENGTH l = conf.payload_size’  >> simp[]
  >- (simp[evaluate_letNONE] >>
      simp[find_evalform ‘App _ _ ’, do_app_thm, store_lookup_def, EL_APPEND2,
           store_assign_def, store_v_same_type_def] >>
      simp[find_evalform ‘Let _ _ _’] >>
      Q.REFINE_EXISTS_TAC ‘clk1 + 1’ >> simp[dec_clock_def] >>
      gs[eval_rel0_thm, SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
      first_x_assum (C (resolve_then (Pos hd) assume_tac)
                     (INST_TYPE [alpha |-> “:plffi”] evaluate_generalise')) >>
      simp[bind_eq_Rval, PULL_EXISTS, AllCaseEqs()] >>
      rename [‘_ = [tkvalf _] ∧ tkf1 _ - 0 ≤ _ ’] >>
      pop_assum kall_tac >>
      qabbrev_tac ‘AR = LUPDATE (7w:word8) 0
                              (REPLICATE (conf.payload_size + 1) 0w)’ >>
      qabbrev_tac ‘refs2 = s.refs ++ [W8array AR]’ >>
      Q.REFINE_EXISTS_TAC ‘tkf1 refs2 + clk1 + 1’>>
      simp[] >>
      gs[Once Arrow_def, AppReturns_thm] >>
      ‘∀n. NUM n (Litv (IntLit (&n)))’ by simp[NUM_def, INT_def] >>
      pop_assum (first_x_assum o resolve_then (Pos (el 2)) assume_tac) >>
      qpat_x_assum ‘_ ⇒ do_opapp [takef; lv] = SOME _’ kall_tac >>
      pop_assum (assume_tac o
                 SRULE [LEFT_FORALL_IMP_THM,
                                       GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])>>
      pop_assum (qx_choosel_then [‘tkclv’, ‘tkexp’] strip_assume_tac) >>
      simp[] >> pop_assum (assume_tac o cj 2) >>
      pop_assum (assume_tac o
                 SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])>>
      pop_assum (qx_choosel_then [‘tk2refs’, ‘tk2val’] assume_tac) >>
      gs[eval_rel0_thm] >>
      pop_assum (assume_tac o
                 SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM,
                                       GSYM LEFT_EXISTS_AND_THM])>>
      pop_assum (qx_choosel_then [‘tk2ck’] assume_tac) >>
      pop_assum (strip_assume_tac o
                 SRULE [PULL_FORALL, IMP_CONJ_THM]) >>
      pop_assum (strip_assume_tac o
                 SRULE [FORALL_AND_THM]) >>
      first_x_assum (C (resolve_then (Pos hd) assume_tac)
                     (INST_TYPE [alpha |-> “:plffi”] evaluate_generalise')) >>
      simp[] >> pop_assum kall_tac >>
      qabbrev_tac ‘takerefs = refs2 ++ tkreff refs2 ++
                              tk2refs refs2 conf.payload_size
                                      (refs2 ++ tkreff refs2)’ >>
      qabbrev_tac
        ‘TKCK =tk2ck refs2 conf.payload_size (refs2 ++ tkreff refs2)’ >>
      Q.REFINE_EXISTS_TAC ‘TKCK + clk1 + 1’ >> simp[] >>
      ‘∃fromListf.
         ∀env.
           env_asm env conf vs ⇒
           (∀yv xv. nsLookup (nsBind "y" yv (nsBind "x" xv env.v))
                             conf.fromList = SOME fromListf) ∧
           (∀l lv.
              DATUM l lv ⇒
              ∃env' exp.
                do_opapp [fromListf; lv] = SOME(env',exp) ∧
                ∀s1: unit semanticPrimitives$state.
                  ∃ck1 ck2.
                    evaluate (s1 with clock := ck1) env' [exp] =
                    (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,
                     Rval [Loc(LENGTH s1.refs)])) ’
        by (simp[env_asm_def, in_module_def, has_v_def, PULL_EXISTS] >>
            qexists_tac ‘EL 7 vs’ >> simp[]) >>
      fs[IMP_CONJ_THM, FORALL_AND_THM] >>
      first_x_assum (first_assum o resolve_then (Pos (el 2)) assume_tac) >>
      pop_assum (assume_tac o
                 SRULE [LEFT_FORALL_IMP_THM]) >>
      pop_assum (assume_tac o
                 SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM])>>
      pop_assum (qx_choosel_then [‘flcl’, ‘flenv’] assume_tac) >> simp[] >>
      pop_assum (assume_tac o
                 SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] o
                 cj 2) >>
      pop_assum (qx_choosel_then [‘flclk1’, ‘flclk2’] assume_tac) >>
      first_x_assum
      (C (resolve_then (Pos hd) assume_tac)
       (INST_TYPE [beta |-> “:plffi”] evaluate_ffi_intro')) >>
      gs[] >>
      pop_assum (assume_tac o
                 Q.GEN ‘t’ o
                 SRULE [] o
                 Q.SPECL [‘t’, ‘ARB with refs := (t:plffi state).refs’]) >>
      first_x_assum
       (C (resolve_then (Pos hd) assume_tac)
        (evaluate_induce_timeout |> cj 1 |> cj 2 |> iffLR)) >>
      gs[] >>
      Q.REFINE_EXISTS_TAC
       ‘(flclk1 (refs2 ++ tkreff refs2) refs2 conf.payload_size
                <| refs := takerefs|> -
         flclk2 (refs2 ++ tkreff refs2) refs2 conf.payload_size
                <| refs := takerefs|>) + clk1’ >> simp[] >>
      ‘LENGTH AR = conf.payload_size + 1’ by simp[Abbr‘AR’] >>
      simp[find_evalform ‘App _ _’, do_app_thm, store_lookup_def, EL_APPEND2,
           Abbr‘takerefs’, Abbr‘refs2’, EL_APPEND1, copy_array_def,
           integerTheory.INT_ADD, store_assign_def, store_v_same_type_def
           ] >>
      simp[state_component_equality] >> simp[TAKE_TAKE_MIN, LUPDATE_APPEND] >>
      simp[LEFT_FORALL_IMP_THM, RIGHT_EXISTS_IMP_THM, EL_APPEND1, EL_APPEND2]>>
      simp[pad_def, Abbr‘AR’, GSYM ADD1, LUPDATE_def, TAKE_LENGTH_ID_rwt]) >>
  simp[find_evalform ‘If _ _ _’, find_evalform ‘App _ _’] >>
  Q.REFINE_EXISTS_TAC ‘clk1 + LENCLK s + 1’ >>
  simp[dec_clock_def, bind_eq_Rval, do_app_thm, opb_lookup_def, do_if_def] >>
  Cases_on ‘LENGTH l < conf.payload_size’ >> simp[]
  >- (simp[evaluate_letNONE, find_evalform ‘App _ _’, do_app_thm,
           store_lookup_def, EL_APPEND1, EL_APPEND2, store_assign_def,
           store_v_same_type_def] >>
      qabbrev_tac
        ‘AR = LUPDATE (6w:word8) 0 (REPLICATE (conf.payload_size + 1) 0w)’ >>
      ‘LENGTH AR = conf.payload_size + 1’ by simp[Abbr‘AR’] >>
      ‘∃fromListf.
         ∀env.
           env_asm env conf vs ⇒
           (∀yv xv. nsLookup (nsBind "y" yv (nsBind "x" xv env.v))
                             conf.fromList = SOME fromListf) ∧
           (∀l lv.
              DATUM l lv ⇒
              ∃env' exp.
                do_opapp [fromListf; lv] = SOME(env',exp) ∧
                ∀s1: unit semanticPrimitives$state.
                  ∃ck1 ck2.
                    evaluate (s1 with clock := ck1) env' [exp] =
                    (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,
                     Rval [Loc(LENGTH s1.refs)])) ’
        by (simp[env_asm_def, in_module_def, has_v_def, PULL_EXISTS] >>
            qexists_tac ‘EL 7 vs’ >> simp[]) >>
      pop_assum (strip_assume_tac o
                 SRULE [IMP_CONJ_THM, FORALL_AND_THM]) >>
      first_x_assum (first_x_assum o resolve_then (Pos (el 2)) assume_tac) >>
      pop_assum (assume_tac o
                 SRULE [LEFT_FORALL_IMP_THM]) >>
      pop_assum (qx_choosel_then [‘flcl’, ‘flenv’] strip_assume_tac o
                 SRULE [GSYM RIGHT_EXISTS_IMP_THM,
                                       IMP_CONJ_THM])>>
      pop_assum (assume_tac o
                 SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM])>>
      pop_assum (qx_choosel_then [‘flclk1’, ‘flclk2’] assume_tac) >>
      first_x_assum
      (C (resolve_then (Pos hd) assume_tac)
       (INST_TYPE [beta |-> “:plffi”] evaluate_ffi_intro')) >>
      gs[] >>
      pop_assum (assume_tac o
                 Q.GEN ‘t’ o
                 SRULE [] o
                 Q.SPECL [‘t’, ‘ARB with refs := (t:plffi state).refs’]) >>
      first_x_assum
       (C (resolve_then (Pos hd) assume_tac)
        (evaluate_induce_timeout |> cj 1 |> cj 2 |> iffLR)) >>
      gs[] >>
      simp[find_evalform ‘Let _ _ _’] >>
      Q.REFINE_EXISTS_TAC ‘clk1 + 1’ >> simp[dec_clock_def] >>
      Q.REFINE_EXISTS_TAC ‘
        (flclk1 <| refs := s.refs ++ [W8array AR]|> -
         flclk2 <| refs := s.refs ++ [W8array AR]|>) + clk1’ >> simp[] >>
      simp[find_evalform ‘App _ _’, do_app_thm, store_lookup_def, EL_APPEND1,
           EL_APPEND2, opn_lookup_def, integerTheory.INT_LT_SUB_RADD,
           integerTheory.INT_SUB, store_assign_def, store_v_same_type_def,
           LUPDATE_APPEND, copy_array_def, integerTheory.INT_ADD] >>
      simp[LEFT_FORALL_IMP_THM, RIGHT_EXISTS_IMP_THM, state_component_equality,
           EL_APPEND1, EL_APPEND2, pad_def] >> strip_tac >>
      simp[Abbr‘AR’, LUPDATE_def, GSYM ADD1, DROP_LENGTH_TOO_LONG] >>
      simp[LIST_EQ_REWRITE, EL_TAKE, EL_LUPDATE] >> rw[]
      >- (Cases_on ‘conf.payload_size - LENGTH l’ >>
          gs[EL_APPEND1, EL_APPEND2] >>
          ‘n + SUC (LENGTH l) - conf.payload_size = 0’ by simp[] >> simp[]) >>
      rename [‘EL i (_ :: _) = _’] >>
      Cases_on ‘i’ >> simp[EL_REPLICATE, EL_APPEND1, EL_APPEND2]) >>
  simp[evaluate_letNONE, find_evalform ‘App _ _’, do_app_thm, store_lookup_def,
       EL_APPEND1, EL_APPEND2, store_assign_def, store_v_same_type_def] >>
  qabbrev_tac
  ‘AR = LUPDATE (2w:word8) 0 (REPLICATE (conf.payload_size + 1) 0w)’ >>
  ‘LENGTH AR = conf.payload_size + 1’ by simp[Abbr‘AR’] >>
  simp[find_evalform ‘Let _ _ _’] >>
  Q.REFINE_EXISTS_TAC ‘clk1 + 1’ >> simp[dec_clock_def] >>
  gs[eval_rel0_thm, SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  first_x_assum (C (resolve_then (Pos hd) assume_tac)
                 (INST_TYPE [alpha |-> “:plffi”] evaluate_generalise')) >>
  simp[bind_eq_Rval, PULL_EXISTS, AllCaseEqs()] >>
  qpat_x_assum ‘_ ⇒ ∀refs. (_ --> _) _ _ ’ assume_tac >>
  gs[Arrow_def, AppReturns_thm] >>
  ‘∀n. NUM n (Litv (IntLit (&n)))’ by simp[NUM_def, INT_def] >>
  pop_assum (first_x_assum o resolve_then (Pos (el 2)) assume_tac) >>
  pop_assum (qx_choosel_then [‘tkenv2’, ‘tkexp2’] assume_tac o
             SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] o
             SRULE [LEFT_FORALL_IMP_THM]) >> simp[] >>
  gs[eval_rel_def] >>
  pop_assum (qx_choosel_then [‘tkrefs2’, ‘tkval2’] assume_tac o
             SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] o
             cj 2) >>
  pop_assum (qx_choosel_then [‘tkclk12’, ‘tkclk22’] assume_tac o
             SRULE [SKOLEM_THM, GSYM LEFT_EXISTS_AND_THM,
                                   GSYM RIGHT_EXISTS_IMP_THM]) >>
  pop_assum (strip_assume_tac o
             SRULE [FORALL_AND_THM, IMP_CONJ_THM]) >>
  qabbrev_tac ‘refs1 = s.refs ++ [W8array AR]’ >>
  rename [‘tkclk1 refs1 ≤ _ ∧ ~(_ ≤ tkclk1 refs1) ∧ _’] >>
  Q.REFINE_EXISTS_TAC ‘tkclk1 refs1 + 1 + clk1’ >> simp[] >>
  first_assum (C (resolve_then (Pos hd) assume_tac) $ cj 1 evaluate_clock) >>
  fs[] >>
  first_x_assum (C (resolve_then (Pos hd) assume_tac)
                 (INST_TYPE [alpha |-> “:plffi”] evaluate_generalise')) >>
  simp[bind_eq_Rval] >> pop_assum kall_tac >>
  qabbrev_tac ‘TKC1 = tkclk12 refs1 conf.payload_size (refs1 ++ tkreff refs1)’>>
  qabbrev_tac ‘TKC2 = tkclk22 refs1 conf.payload_size (refs1 ++ tkreff refs1)’>>
  ‘(∃env. env_asm env conf vs) ⇒ TKC2 ≤ TKC1’ by simp[Abbr‘TKC1’, Abbr‘TKC2’] >>
  rpt
    (first_x_assum (kall_tac o assert (free_in “tkclv : v sem_env” o concl)))>>
  Q.REFINE_EXISTS_TAC ‘TKC1 - TKC2 + 1 + clk1’ >> simp[] >>
  simp[DECIDE “y ≤ x ⇒ x:num - y + 1 + Z + y - (x + 1) = Z”] >>
  map_every (Q_TAC (fn t =>
                      rpt (first_x_assum (kall_tac o
                                          assert (free_in t o concl)))))
            [‘tkclk12’, ‘tkclk22’, ‘TKC1’, ‘TKC2’] >>
  ‘∃fromListf.
     ∀env.
       env_asm env conf vs ⇒
       (∀yv xv. nsLookup (nsBind "y" yv (nsBind "x" xv env.v))
                         conf.fromList = SOME fromListf) ∧
       (∀l lv.
          DATUM l lv ⇒
          ∃env' exp.
            do_opapp [fromListf; lv] = SOME(env',exp) ∧
            ∀s1: unit semanticPrimitives$state.
              ∃ck1 ck2.
                evaluate (s1 with clock := ck1) env' [exp] =
                (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,
                 Rval [Loc(LENGTH s1.refs)])) ’
    by (simp[env_asm_def, in_module_def, has_v_def, PULL_EXISTS] >>
        qexists_tac ‘EL 7 vs’ >> simp[]) >>
  pop_assum (strip_assume_tac o
             SRULE [IMP_CONJ_THM, FORALL_AND_THM]) >>
  first_x_assum (first_x_assum o resolve_then (Pos (el 2)) assume_tac) >>
  pop_assum (assume_tac o
             SRULE [LEFT_FORALL_IMP_THM]) >>
  pop_assum (qx_choosel_then [‘flcl’, ‘flenv’] strip_assume_tac o
             SRULE [GSYM RIGHT_EXISTS_IMP_THM,
                                   IMP_CONJ_THM, SKOLEM_THM])>>
  pop_assum (strip_assume_tac o SRULE [FORALL_AND_THM]) >>
  pop_assum (assume_tac o SRULE [SKOLEM_THM])>>
  pop_assum (qx_choosel_then [‘flclk1’, ‘flclk2’] assume_tac) >>
  first_x_assum
  (C (resolve_then (Pos hd) assume_tac)
   (INST_TYPE [beta |-> “:plffi”] evaluate_ffi_intro')) >>
  gs[] >>
  pop_assum (assume_tac o
             Q.GEN ‘t’ o
             SRULE [] o
             Q.SPECL [‘t’, ‘ARB with refs := (t:plffi state).refs’]) >>
  first_x_assum
  (C (resolve_then (Pos hd) assume_tac)
   (evaluate_induce_timeout |> cj 1 |> cj 2 |> iffLR)) >>
  gs[] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (s with <| clock := _; refs := RFS |>)’>>
  Q.REFINE_EXISTS_TAC
   ‘clk1 + flclk1 (refs1 ++ tkreff refs1) refs1 conf.payload_size
                  <| refs := RFS|>’ >> simp[] >>
  simp[find_evalform ‘App _ _’, do_app_thm, copy_array_def, EL_APPEND1,
       EL_APPEND2, store_lookup_def, Abbr‘RFS’, Abbr‘refs1’,
       integerTheory.INT_ADD, store_assign_def, store_v_same_type_def,
       LUPDATE_APPEND] >>
  simp[LEFT_FORALL_IMP_THM, state_component_equality, RIGHT_EXISTS_IMP_THM,
       EL_APPEND1, EL_APPEND2] >>
  simp[Abbr‘AR’, GSYM ADD1, DROP_LENGTH_TOO_LONG, LUPDATE_def, TAKE_TAKE_T,
       pad_def]
QED

Theorem env_asm_lenf_sem0:
  ∃lenf.
     (∀k v env. env_asm env conf vs ⇒ nsLookup env.v conf.length = SOME lenf) ∧
     ((∃env. env_asm env conf vs) ⇒ (DATUM ~~> NUM) LENGTH lenf)
Proof
  simp[env_asm_def, in_module_def, has_v_def, at_def] >>
  qexists_tac ‘EL 2 vs’ >> simp[] >> metis_tac[]
QED

Theorem env_asm_dropf_sem0:
  ∃dropf.
    (∀v env. env_asm env conf vs ⇒ nsLookup env.v conf.drop = SOME dropf) ∧
    ((∃env. env_asm env conf vs) ⇒ (DATUM ~~> NUM ~~> DATUM) (flip DROP) dropf)
Proof
  simp[env_asm_def, in_module_def, has_v_def, at_def] >>
  qexists_tac ‘EL 5 vs’ >> simp[] >> metis_tac[]
QED

Theorem env_asm_appendf_sem0:
  ∃appf.
    (∀v env. env_asm env conf vs ⇒ nsLookup env.v conf.append = SOME appf) ∧
    ((∃env. env_asm env conf vs) ⇒
     (LIST_TYPE DATUM ~~> LIST_TYPE DATUM ~~> LIST_TYPE DATUM) $++ appf)
Proof
  simp[env_asm_def, in_module_def, has_v_def, at_def] >>
  qexists_tac ‘HD vs’ >> simp[] >> metis_tac[]
QED

Theorem env_asm_concatf_sem0:
  ∃concatf.
    (∀v env. env_asm env conf vs ⇒ nsLookup env.v conf.concat = SOME concatf) ∧
    ((∃env. env_asm env conf vs) ⇒ (LIST_TYPE DATUM ~~> DATUM) FLAT concatf)
Proof
  simp[env_asm_def, in_module_def, has_v_def, at_def] >>
  qexists_tac ‘EL 1 vs’ >> simp[] >> metis_tac[]
QED

Theorem env_asm_reversef_sem0:
  ∃revf.
    (∀v env. env_asm env conf vs ⇒ nsLookup env.v conf.reverse = SOME revf) ∧
    ((∃env. env_asm env conf vs) ⇒
     (LIST_TYPE DATUM ~~> LIST_TYPE DATUM) REVERSE revf)
Proof
  simp[env_asm_def, in_module_def, has_v_def, at_def] >>
  qexists_tac ‘EL 6 vs’ >> simp[] >> metis_tac[]
QED

Theorem env_asm_LENGTH =
  env_asm_lenf_sem0
      |> SRULE [reffree_AppReturns_def, reffree_Arrow_def,
                eval_rel0_thm, NUM_def, INT_def]
      |> underEXs (atcj 2
                   (GENL [“l:word8 list”, “lv : v”] o DISCH “DATUM l lv” o
                    DISCH “∃env. env_asm env conf vs” o
                    C MATCH_MP (ASSUME “DATUM l lv”) o UNDISCH))
      |> SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_AND_THM,
                GSYM RIGHT_EXISTS_IMP_THM]
      |> CONV_RULE (RENAME_VARS_CONV ["lenf", "lencl_env", "lencl_exp",
                                      "lenclk"])
      |> underEXs $ atcj 2 $ underAIs $ atcj 2 $
          underAIs (MATCH_MP evaluate_generalise')
      |> INST_TYPE [alpha |-> “:plffi”] |> SRULE[]

Theorem clock_selfupdate[simp,local]:
  s with clock := s.clock = s
Proof
  simp[state_component_equality]
QED

Theorem env_asm_DROP =
  env_asm_dropf_sem0
      |> SRULE [reffree_AppReturns_def, reffree_Arrow_def,
                eval_rel0_thm, NUM_def, INT_def, GSYM LEFT_EXISTS_AND_THM]
      |> underEXs (atcj 2
                   (GENL [“l:word8 list”, “lv : v”] o DISCH “DATUM l lv” o
                    DISCH “∃env. env_asm env conf vs” o
                    C MATCH_MP (ASSUME “DATUM l lv”) o UNDISCH))
      |> SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_AND_THM,
                GSYM RIGHT_EXISTS_IMP_THM]
      |> CONV_RULE (RENAME_VARS_CONV ["dropf", "drop1cl_env", "drop1cl_exp",
                                      "drop1_v", "drop1clk",
                                      "drop2cl_env", "drop2cl_exp",
                                      "drop2_v", "drop2clk"])
      |> underEXs $ atcj 2 $ underAIs $ atcj 2 $
          underAIs $ atcj 1 $ MATCH_MP evaluate_generalise'
      |> SRULE[PULL_FORALL]
      |> underEXs $ underAIs $ atcj 2 $ underAIs $ atcj 4 $
          MATCH_MP evaluate_generalise'
      |> underEXs $
          CONV_RULE (EVERY_CONV
                     (map pull_namedallvar_conv ["st", "refs", "nc1"]))
      |> underEXs $
           (Q.GEN ‘st’ o Q.SPECL [‘st.clock’, ‘(st:'a state).refs’, ‘st’])
      |> INST_TYPE [alpha |-> “:plffi”] |> SRULE[PULL_FORALL]
      |> underEXs $
          CONV_RULE (EVERY_CONV
                     (map pull_namedallvar_conv ["st'", "refs'", "nc1"]))
      |> underEXs $
           (Q.GEN ‘st1’ o
            Q.SPECL [‘(st1:plffi state).clock’, ‘(st1:plffi state).refs’,
                     ‘st1’])
      |> SRULE[]

Theorem env_asm_APPEND =
        env_asm_appendf_sem0
          |> SRULE [reffree_AppReturns_def, reffree_Arrow_def, eval_rel0_thm,
                    GSYM LEFT_EXISTS_AND_THM]
          |> underEXs (atcj 2
                       (GENL [“l1:word8 list list”, “lv1 : v”] o
                        DISCH “LIST_TYPE DATUM l1 lv1” o
                        DISCH “∃env. env_asm env conf vs” o
                        C MATCH_MP (ASSUME “LIST_TYPE DATUM l1 lv1”) o UNDISCH))

Theorem env_asm_FLAT =
        env_asm_concatf_sem0
          |> SRULE [reffree_AppReturns_def, reffree_Arrow_def, eval_rel0_thm,
                    GSYM LEFT_EXISTS_AND_THM]
          |> underEXs (atcj 2
                       (GENL [“l1:word8 list list”, “lv1 : v”] o
                        DISCH “LIST_TYPE DATUM l1 lv1” o
                        DISCH “∃env. env_asm env conf vs” o
                        C MATCH_MP (ASSUME “LIST_TYPE DATUM l1 lv1”) o UNDISCH))


Theorem in_module_nsLookup_nsBind:
  in_module id ⇒
  nsLookup (nsBind k v ns:(string,string,v)namespace) id = nsLookup ns id
Proof
  simp[in_module_def]
QED

Theorem in_module_nsLookup_build_rec_env:
  in_module id ⇒ nsLookup (build_rec_env fs e0 ns) id = nsLookup ns id
Proof
  simp[in_module_def] >>
  simp[build_rec_env_def] >> qabbrev_tac ‘rc = Recclosure e0 fs’ >>
  RM_ABBREV_TAC "rc" >> Induct_on ‘fs’ >> simp[FORALL_PROD]
QED

Overload sendloop_code[local] =
  (list_mk_abs([“conf : config”, “dest : string”],
               sendloop_def |> concl |> strip_forall |> #2 |> rhs |> rator
                 |> rand |> pairSyntax.strip_pair |> last))

Theorem sendloop_correct:
  ∀conf l lv vs (s:plffi state) stpred dest slv.
    DATUM l lv ∧ conf.payload_size ≠ 0 ∧ stpred s.ffi.ffi_state ∧
    ffi_accepts_rel stpred (valid_send_call_format conf dest) s.ffi.oracle ∧
    Abbrev (slv = λe. Recclosure e (sendloop conf (MAP (CHR o w2n) dest))
                                 "sendloop")
    ⇒
    ∃ck1 ck2 refs'.
      ∀env1.
        env_asm env1 conf vs ⇒
        ∃env2 body.
          do_opapp [slv env1; lv] = SOME (env2, body) ∧
          evaluate (s with clock:= ck1) env2 [body] =
          (s with <|
             clock := ck2; refs := s.refs ++ refs';
             ffi:= s.ffi with
                    <|io_events := s.ffi.io_events ++
                                   send_events conf dest l;
                      ffi_state := update_state s.ffi.ffi_state
                                                s.ffi.oracle
                                                (send_events conf dest l)
                    |>
           |> , Rval [Conv NONE []])
Proof
  ho_match_mp_tac compile_message_ind>> rpt strip_tac >> simp[] >>
  qabbrev_tac ‘
   sltriple = [("sendloop", "x", sendloop_code conf (MAP (CHR o w2n) dest))]’ >>
  qabbrev_tac ‘slE = λv E. nsBind "x" v (build_rec_env sltriple E E.v)’ >>
  ‘∀v E. nsLookup (slE v E) (Short "x") = SOME v’ by simp[Abbr‘slE’] >>
  ‘∀E vl. do_opapp [slv E; vl] =
          SOME (E with v := slE vl E,sendloop_code conf (MAP (CHR o w2n) dest))’
    by (simp[Abbr‘slv’, Abbr‘sltriple’, do_opapp_def, sendloop_def, Abbr‘slE’,
             Once find_recfun_def]) >>
  simp[find_evalform ‘Let _ _ _’, bind_eq_Rval, PULL_EXISTS, AllCaseEqs()] >>
  ‘∀E v. env_asm E conf vs ⇒ env_asm (E with v := slE v E) conf vs’
    by simp[Abbr‘slE’, env_asm_def, at_def, has_v_def, in_module_def,
            Abbr‘sltriple’, build_rec_env_def] >>
  drule_then (qspecl_then [‘vs’, ‘conf’, ‘s’] strip_assume_tac) padv_correct'>>
  pop_assum (qx_choosel_then [‘pclv’, ‘pbode’, ‘pE'’] strip_assume_tac o
             SRULE [FORALL_AND_THM, IMP_CONJ_THM] o
             SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM]) >>
  simp[] >>
  last_x_assum (C(resolve_then (Pos hd)
                  (assume_tac o cj 2 o SRULE []))$
                cj 1 evaluate_induce_timeout) >>
  simp[dec_clock_def] >> Q.REFINE_EXISTS_TAC ‘clk1 + 1’ >> simp[] >>
  pop_assum kall_tac (* dropping evaluate (padv conf) *) >>
  last_assum (C(resolve_then (Pos hd)
                (assume_tac o SRULE [])) $
              cj 1 evaluate_clock) >>
  last_x_assum (C(resolve_then (Pos hd)
                  (assume_tac o iffLR o cj 2 o SRULE []))$
                cj 1 evaluate_induce_timeout) >>
  Q.REFINE_EXISTS_TAC ‘clk1 + ck1 - ck2’ >>
  simp[DECIDE “y:num ≤ x ⇒ x + Z - y + y - x = Z”] >>
  map_every
    (Q_TAC (fn t => rpt (first_x_assum(kall_tac o assert(free_in t o concl)))))
    [‘pclv’, ‘pbode’] >>
  simp[find_evalform ‘App _ _’, do_app_thm, AllCaseEqs(), PULL_EXISTS] >>
  gs[ffi_accepts_rel_def] >>
  first_assum $
     drule_then (assume_tac o
                 SIMP_RULE(srw_ss()) [valid_send_call_format_def]) >>
  simp[call_FFI_def] >>
  pop_assum $
    qspec_then ‘pad conf l’ (assume_tac o SRULE [pad_LENGTH]) >>
  gs[store_lookup_def, store_assign_def, store_v_same_type_def] >>
  qpat_abbrev_tac ‘FF = _.ffi with <| ffi_state := _; io_events := _|>’ >>
  simp[find_evalform ‘If _ _ _ ’, bind_eq_Rval, AllCaseEqs(), PULL_EXISTS,
       find_evalform ‘App _ _’, do_app_thm, payload_size_def] >>
  ‘(∃env vs. env_asm env conf vs) ⇒ in_module conf.length ∧ in_module conf.drop’
    by (simp[env_asm_def] >> metis_tac[]) >>
  ‘∀id x e. in_module id ⇒ nsLookup (slE x e) id = nsLookup e.v id’
    by simp[Abbr‘slE’, in_module_nsLookup_nsBind,
            in_module_nsLookup_build_rec_env] >>
  simp[in_module_nsLookup_nsBind] >>
  strip_assume_tac env_asm_LENGTH >> pop_assum $ drule_then assume_tac >>
  simp[dec_clock_def] >>
  Q.REFINE_EXISTS_TAC ‘clk1 + 1’ >> simp[] >>
  qpat_abbrev_tac ‘LCLK = lenclk _ _ (LUPDATE _ _ _)’ >>
  Q.REFINE_EXISTS_TAC ‘LCLK + clk1’ >>
  simp[do_if_def, do_app_thm, opb_lookup_def] >> ntac 3 (pop_assum kall_tac) >>
  Cases_on ‘LENGTH l ≤ conf.payload_size’ >> simp[]
  >- (simp[find_evalform ‘Con _ _’, do_con_check_def, build_conv_def] >>
      simp[LEFT_FORALL_IMP_THM, RIGHT_EXISTS_IMP_THM,
           state_component_equality, Abbr‘FF’] >>
      simp[GSYM LEFT_FORALL_IMP_THM, LUPDATE_SAME']>>
      ‘final (pad conf l)’ by rw[pad_def, final_def] >>
      simp[send_events_def] >> ONCE_REWRITE_TAC [compile_message_def] >>
      simp[update_state_def]) >>
  simp[find_evalform ‘Let _ _ _’, bind_eq_Rval, PULL_EXISTS, AllCaseEqs(),
       dec_clock_def] >> Q.REFINE_EXISTS_TAC ‘clk1 + 1’ >>
  simp[in_module_nsLookup_nsBind] >>
  strip_assume_tac env_asm_DROP >> simp[] >>
  pop_assum (drule_then assume_tac o cj 2) >> simp[] >>
  qpat_abbrev_tac ‘DCK1 = drop1clk _ _ _ ’ >>
  Q.REFINE_EXISTS_TAC ‘DCK1 + clk1 + 1’ >> simp[] >>
  pop_assum kall_tac >>
  pop_assum (fn th => map_every (fn i => assume_tac (cj i th)) [5,4,3]) >>
  pop_assum
    (assume_tac o SRULE [Once FORALL_state] o CONV_RULE SWAP_FORALL_CONV) >>
  simp[] >> pop_assum kall_tac >>
  pop_assum
    (assume_tac o SRULE [Once FORALL_state] o CONV_RULE SWAP_FORALL_CONV) >>
  simp[] >> pop_assum kall_tac >>
  ‘¬final (pad conf l)’ by rw[pad_def, final_def] >> fs[] >>
  last_x_assum (drule_at_then (Pos last) assume_tac) >>
  ‘∀E. nsLookup (slE lv E) (Short "sendloop") = SOME (slv E)’
    by simp[Abbr‘slE’, build_rec_env_def, Abbr‘sltriple’, Abbr‘slv’,
            sendloop_def] >>
  qpat_x_assum ‘∀E vl. do_opapp [slv E; vl] = _’ kall_tac >> simp[] >>
  qpat_abbrev_tac ‘DCL2 = drop2clk _ _ _ _ _ ’ >>
  Q.REFINE_EXISTS_TAC ‘DCL2 + clk1 + 1’ >> simp[] >>
  ntac 2 (pop_assum kall_tac) >>
  pop_assum (assume_tac o CONV_RULE (pull_namedallvar_conv "s'")) >>
  simp[LUPDATE_SAME'] >>
  pop_assum $
     qspec_then ‘s with <| refs := s.refs ++ refs ;
                           ffi := FF |>’ (assume_tac o SRULE[]) >>
  ‘FF.oracle = s.ffi.oracle ∧ FF.ffi_state = ffi’ by simp[Abbr‘FF’] >> fs[] >>
  first_x_assum (drule_at_then (Pos last) assume_tac) >>
  pop_assum (drule_at_then (Pos last) assume_tac) >>
  pop_assum (first_x_assum o C (resolve_then (Pos hd) assume_tac)) >>
  pop_assum (strip_assume_tac o
             SRULE [GSYM RIGHT_EXISTS_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
                    AND_IMP_INTRO] o
             SRULE [LEFT_FORALL_IMP_THM]) >>
  pop_assum (qspec_then ‘vs’ assume_tac) >>
  pop_assum (assume_tac o SIMP_RULE (srw_ss() ++ CONJ_ss) []) >>
  pop_assum (assume_tac o SRULE [RIGHT_EXISTS_IMP_THM]) >>
  pop_assum $ assume_tac o SRULE [FORALL_state] >>
  pop_assum $
    qspecl_then [‘s.refs ++ refs’, ‘s.refs ++ refs’] $
      qx_choosel_then [‘CK1’, ‘CK2’, ‘REFS'’] assume_tac >>
  qexistsl_tac [‘CK1’, ‘CK2’, ‘refs ++ REFS'’] >> rpt strip_tac >>
  first_x_assum $ drule_all_then strip_assume_tac >> simp[] >>
  simp[state_component_equality, Abbr‘FF’, ffi_state_component_equality] >>
  gs[send_events_def] >>
  ‘compile_message conf l =
   pad conf l :: compile_message conf (DROP conf.payload_size l)’
    by simp[Once compile_message_def, SimpLHS] >> simp[update_state_def]
QED

Theorem nsLookup_sendloop_exists:
  ∃slv. nsLookup (build_rec_env(sendloop conf data) cE cEv) (Short "sendloop") =
        SOME slv
Proof
  simp[build_rec_env_def, sendloop_def]
QED

Theorem ALL_DISTINCT_sendloop_names[simp]:
  ALL_DISTINCT (MAP (λ(x,y,z). x) (sendloop conf data))
Proof
  simp[sendloop_def]
QED

Theorem nsLookup_sendloop[simp]:
  nsLookup (build_rec_env (sendloop conf data) env envv) (Short (ps2cs v)) =
  nsLookup envv (Short (ps2cs v))
Proof
  simp[build_rec_env_def, ps2cs_def, nsLookup_def, sendloop_def]
QED

(* RECEIVELOOP CORRECT *)
(* List of IO events to receive a piece of data *)
Definition receive_events_def:
  receive_events conf bufInit src d =
  let
    msgChunks  = compile_message conf d;
    data_pairs = ZIP (bufInit::msgChunks,msgChunks)
  in
    MAP (λ(a,b). IO_event "receive" src (ZIP (a,b))) data_pairs
End

(* HOL Model of CakeML find_one function *)
(* -- Definition of model *)
Definition hfind_one_def:
  hfind_one n l =
    if (LENGTH l ≤ n) then
      LENGTH l
    else
      if (1w = EL n l) then
        n
      else
        hfind_one (SUC n) l
Termination
  WF_REL_TAC ‘measure (λ(n,l). LENGTH l - n)’
End

(* -- Model matches CakeML *)
Theorem ALL_DISTINCT_find_one[simp]:
  ALL_DISTINCT (MAP (λ(x,y,z). x) find_one)
Proof
  simp[find_one_def]
QED

Theorem find_one_equiv:
  ∀env lnum s1 l n.
    nsLookup     env.v (Short "x") = SOME (Loc lnum) ∧
    store_lookup lnum  s1.refs     = SOME (W8array l) ⇒
    ∃ck1 ck2 rv.
      evaluate$evaluate (s1 with clock := ck1) env
                      [Letrec find_one
                        (App Opapp [Var (Short "find_one");
                                    Lit (IntLit &n)])]
      = (s1 with clock := ck2, Rval [rv]) ∧
      NUM (hfind_one n l) rv
Proof
  rw[] >>
  completeInduct_on ‘LENGTH l - n’ >>
  rw (find_one_def::(Once find_recfun_def)::eval_sl) >>
  qmatch_goalsub_abbrev_tac ‘App Opapp [Var (Short "find_one"); rec_value]’ >>
  qabbrev_tac ‘rec_call = App Opapp [Var (Short "find_one"); rec_value]’ >>
  qunabbrev_tac ‘rec_value’ >>
  Q.REFINE_EXISTS_TAC ‘SUC ck1’ >> rw (ADD1::dec_clock_def::eval_sl) (* 3 *)
  >- (‘LENGTH l ≤ n’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw (Once hfind_one_def::trans_sl) >>
      metis_tac[])
  >- (‘LENGTH l > n’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw (Once hfind_one_def::(trans_sl@eval_sl)) >> fs[] (* 2 *)
      >- metis_tac[]
      >- (rpt (qpat_x_assum ‘T’ (K ALL_TAC)) >>
          first_x_assum (qspec_then ‘LENGTH l - (n + 1)’ assume_tac) >>
          rfs[] >>
          first_x_assum (qspecl_then [‘l’,‘n + 1’] assume_tac) >>
          rfs(ADD1::store_lookup_def::trans_sl)  >>
          qexistsl_tac [‘ck1’,‘ck2’] >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m envM _’ >>
          qmatch_asmsub_abbrev_tac ‘evaluate s1m env [irecexp]’ >>
          ‘evaluate s1m envM [rec_call] = evaluate s1m env [irecexp]’
            suffices_by rw[] >>
          qpat_x_assum ‘evaluate s1m env [irecexp] = _’ (K ALL_TAC) >>
          qunabbrev_tac ‘irecexp’ >>
          qunabbrev_tac ‘rec_call’ >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m envM IGNORE’ >>
          qmatch_goalsub_abbrev_tac
            ‘evaluate s1m env [Letrec find_one IGNORE2]’ >>
          rw eval_sl >>
          EVAL_TAC >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m envMR [IGNORE2]’ >>
          ‘envM = envMR with v := nsBind "n" (Litv (IntLit (&n))) envMR.v’
            by (qunabbrev_tac ‘envM’ >> qunabbrev_tac ‘envMR’ >> simp[]) >>
          rw[] >>
          qunabbrev_tac ‘IGNORE’ >> qunabbrev_tac ‘IGNORE2’ >>
          PURE_ONCE_REWRITE_TAC [evaluate_def] >>
          simp[] >>
          qabbrev_tac ‘IGNORE = do_opapp’ >>
          rw eval_sl >>
          ‘(((&(n :num)) :int) + 1) = ((&(n + (1 :num))) :int)’
            suffices_by rw[] >>
          intLib.COOPER_TAC))
  >- (Cases_on ‘LENGTH l ≤ n’ >> fs eval_sl)
QED

Theorem nsLookup_build_rec_env_find_one[simp]:
  nsLookup (build_rec_env find_one e v) (Short "find_one") =
  SOME (Recclosure e find_one "find_one")
Proof
  simp[find_one_def, build_rec_env_def]
QED

Overload find_one_code[local] =
  (find_one_def |> concl |> rhs |> lhand |> rand |> rand)

Theorem find_recfun_find_one[simp]:
  find_recfun "find_one" find_one =
  SOME ("n", find_one_code)
Proof
  simp[find_one_def, Once find_recfun_def]
QED

Overload unpadv_code[local] =
  (list_mk_abs([“conf : config”],
               unpadv_def |> concl |> strip_forall |> #2 |> rhs |> rand))

Theorem min1SUC[local,simp]:
  MIN 1 (SUC x) = 1
Proof
  simp[MIN_DEF]
QED

Theorem findi_LE_LENGTH[simp]:
  findi x l ≤ LENGTH l
Proof
  Induct_on‘l’ >> simp[findi_def, ADD1] >> rw[]
QED

Theorem findi_EL_DROP:
  ∀p l. p < LENGTH l ⇒ findi (EL p l) (DROP p l) = 0
Proof
  Induct_on ‘p’ >> Cases_on ‘l’ >> simp[findi_def]
QED

Theorem findi_splitp:
  findi x l = LENGTH (FST (SPLITP ((=) x) l))
Proof
  Induct_on ‘l’ >> simp[findi_def, SPLITP] >> rw[]
QED

(* -- Model, and thus CakeML code also, correctly simulates SPLITP  *)
Theorem hfind_one_findi:
  ∀n l. hfind_one n l = MIN n (LENGTH l) + findi 1w (DROP n l)
Proof
  rpt gen_tac >> Induct_on ‘LENGTH l - n’ >>
  simp[findi_def, Once hfind_one_def, DROP_LENGTH_TOO_LONG]
  >- simp[MIN_DEF] >>
  Cases_on ‘l’ >> simp[] >> rpt strip_tac >>
  rename [‘SUC m = SUC (LENGTH ll) - n’] >>
  Cases_on ‘n’ >> simp[]
  >- (Cases_on ‘h = 1w’ >> simp[findi_def, MIN_DEF]) >>
  rename [‘1w = EL p ll’]>> ‘p < LENGTH ll’ by simp[] >>
  ‘m + p + 1 = LENGTH ll’ by simp[]  >>
  ‘MIN (SUC p) (SUC (LENGTH ll)) = SUC p ∧
   MIN (SUC (SUC p)) (SUC (LENGTH ll)) = SUC (SUC p)’ by simp[MIN_DEF] >>
  rw[ADD_CLAUSES, DECIDE “x:num = x + y ⇔ y = 0”, findi_EL_DROP] >>
  simp[DROP_CONS_EL, findi_def]
QED

Theorem find_recfun_thm[simp]:
  find_recfun n [] = NONE ∧
  find_recfun n ((f,x,e) :: rest) = if f = n then SOME (x,e)
                                    else find_recfun n rest
Proof
  strip_tac >> simp[Once find_recfun_def]
QED

Theorem env_asm_ignores_nsBindings[simp]:
  env_asm (e with v := nsBind k value v') conf vs ⇔
  env_asm (e with v:= v') conf vs
Proof
  simp[env_asm_def, in_module_def, has_v_def]>> csimp[]
QED

Theorem SEG_SUC_SNOC:
  ∀n start l.
    0 < n ∧ start + n ≤ LENGTH l ⇒
    SEG n start l = SEG (n - 1) start l ++ [EL (start + n - 1) l]
Proof
  Induct_on ‘l’ >> simp[] >> rpt strip_tac >> Cases_on ‘n’ >>
  Cases_on ‘start’ >> gs[ADD_CLAUSES]
  >- (gs[SEG] >> rename [‘h::SEG m 0 l’] >> Cases_on ‘m’
      >- simp[SEG] >> simp[] >> simp[SEG])
  >- (simp[SEG] >> reverse conj_tac
      >- (‘∀x y. x + SUC y - 1 = x + y’ by simp[] >> simp[]) >>
      rename [‘SEG m n l = SEG m _ _’] >> Cases_on ‘m’ >> simp[SEG])
QED

Theorem backseg_correct:
  ∀idx list Av e e0 srefs i ds start.
    env_asm e0 conf cvs ∧ env_asm e conf cvs ∧
    i < LENGTH srefs ∧ EL i srefs = W8array ds ∧
    LENGTH ds ≠ 0 ∧ start ≤ idx ∧ idx < LENGTH ds ∧
    nsLookup e.v (Short "x") = SOME (Loc i) ∧
    nsLookup e0.v (Short "x") = SOME (Loc i) ∧
    nsLookup e.v (Short "i") = SOME (Litv (IntLit (&idx))) ∧
    nsLookup e.v (Short "n") = SOME (Litv (IntLit (&start))) ∧
    nsLookup e0.v (Short "n") = SOME (Litv (IntLit (&start))) ∧
    nsLookup e.v (Short "A") = SOME Av ∧ DATUM list Av ∧
    nsLookup e.v (Short "backseg") =
    SOME (Recclosure e0 [("backseg", "A", Fun "i" (backseg_code conf))]
          "backseg")
    ⇒
    ∃ck1 ck2 resv.
      evaluate ((s with <| clock := ck1; refs := srefs |>) :
                unit semanticPrimitives$state) e
               [backseg_code conf] =
      (s with <| clock := ck2; refs := srefs |>, Rval [resv]) ∧
      DATUM (SEG (idx - start) (start + 1) ds ++ list) resv
Proof
  Induct >> csimp[] >>
  simp[evaluate_def, backseg_code_def, do_app_thm, do_if_def,
       opb_lookup_def, SEG]
  >- metis_tac[] >>
  rpt strip_tac >> rw[]
  >- (‘SUC idx = start’ by simp[] >> simp[SEG] >> metis_tac[]) >>
  gs[NOT_LESS_EQUAL] >>
  ‘nsLookup e.c conf.cons = SOME (2, TypeStamp "::" list_type_num) ∧
   nsLookup e.c conf.nil = SOME (0, TypeStamp "[]" list_type_num)’
    by gvs[env_asm_def, has_v_def] >>
  simp[GSYM backseg_code_def] >>
  simp[evaluate_def, do_app_thm, do_con_check_def, store_lookup_def,
       build_conv_def, do_opapp_def] >>
  Q.REFINE_EXISTS_TAC ‘ck1 + 1’ >> simp[dec_clock_def]>>
  Q.REFINE_EXISTS_TAC ‘ck1 + 1’ >> simp[dec_clock_def]>>
  simp[opn_lookup_def, evaluate_def, build_rec_env_def, do_app_thm,
       do_if_def, opb_lookup_def, integerTheory.INT_SUB] >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ ENV _ = _’ >>
  ‘env_asm ENV conf cvs’ by simp[Abbr‘ENV’] >>
  first_x_assum $ drule_at (Pos (el 2)) >>
  simp[Abbr‘ENV’] >> disch_then $ qspec_then ‘EL (SUC idx) ds :: list’ mp_tac >>
  simp[LIST_TYPE_def, WORD_def, list_type_num_def, PULL_EXISTS] >>
  disch_then $ drule_then drule >> simp[] >>
  strip_tac >> simp[] >>
  first_assum $ irule_at Any >>
  simp[SEG_SUC_SNOC, DECIDE “SUC x - (y + 1) = x - y”,
       GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]
QED

Theorem hfind_one_bound:
  ∀i l. i ≤ LENGTH l ⇒ hfind_one i l ≤ LENGTH l
Proof
  recInduct hfind_one_ind >> rpt strip_tac >> simp[Once hfind_one_def] >>
  rw[]
QED

Theorem min_lemma[local,simp]:
  MIN 1 (x + 1) = 1
Proof
  simp[MIN_DEF]
QED

Theorem zerobuf_correct:
  ∀i e srefs ds.
    j < LENGTH srefs ∧ EL j srefs = W8array ds ∧ i < LENGTH ds ∧
    nsLookup e.v (Short "i") = SOME (Litv (IntLit &i)) ∧
    nsLookup e.v (Short "buff") = SOME (Loc j) ∧
    nsLookup e0.v (Short "buff") = SOME (Loc j) ∧
    nsLookup e.v (Short "zerobuf") =
    SOME (Recclosure e0 [("zerobuf", "i", zerobuf_code)] "zerobuf")
    ⇒
    ∃ck1 ck2.
      evaluate ((s with <| clock := ck1; refs := srefs |>) :
                plffi semanticPrimitives$state) e
               [zerobuf_code] =
      (s with <|
         clock := ck2;
         refs := LUPDATE (W8array (REPLICATE (i + 1) 0w ++ DROP (i + 1) ds))
                         j
                         srefs
              |>,
       Rval [Conv NONE []])
Proof
  Induct >> rpt strip_tac >>
  simp[zerobuf_code_def, find_evalform ‘If _ _ _’, find_evalform ‘App _ _’,
       find_evalform ‘Con _ _’, do_app_thm, do_if_def, opb_lookup_def] >>
  simp[find_evalform ‘Let _ _ _’, do_opapp_def, find_evalform ‘App _ _’,
       do_app_thm, store_lookup_def, store_assign_def, store_v_same_type_def,
       AllCaseEqs(), dec_clock_def]
  >- (simp[zerobuf_code_def, find_evalform ‘If _ _ _’, find_evalform ‘App _ _’,
           find_evalform ‘Con _ _’, do_app_thm, do_if_def, opb_lookup_def,
           opn_lookup_def, do_con_check_def, build_conv_def] >>
      simp[state_component_equality] >> qexists_tac ‘SUC 0’ >> simp[] >>
      Cases_on ‘ds’ >> gs[LUPDATE_def, REPLICATE_compute]) >>
  gs[] >>
  qmatch_goalsub_abbrev_tac
    ‘evaluate (s with <| clock := _; refs := rfs|>) ENV [zerobuf_code]’ >>
  first_x_assum $ qspecl_then [‘ENV’, ‘rfs’] mp_tac >>
  simp[Abbr‘ENV’, Abbr‘rfs’, opn_lookup_def, build_rec_env_def,
       EL_LUPDATE, integerTheory.INT_SUB] >>
  disch_then $ qx_choosel_then [‘ck1’, ‘ck2’] strip_assume_tac >>
  qexists_tac ‘ck1 + 1’ >> simp[] >>
  simp[state_component_equality, LUPDATE_LUPDATE_c] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[GSYM ADD1] >> Cases_on ‘ds’ >> gs[LUPDATE_def] >>
  simp[LIST_EQ_REWRITE] >> qx_gen_tac ‘k’ >> strip_tac >>
  Cases_on ‘k’ >> simp[]
  >- (Cases_on ‘i’ >> simp[LUPDATE_def] >> Cases_on ‘t’ >> gs[LUPDATE_def]) >>
  rename [‘SUC k0 < LENGTH t’] >> Cases_on ‘SUC k0 < i’
  >- simp[EL_APPEND1, EL_REPLICATE] >>
  simp[EL_APPEND2, EL_DROP, EL_LUPDATE] >> Cases_on ‘SUC k0 ≤ i’ >>
  simp[EL_APPEND1, EL_APPEND2, EL_REPLICATE, EL_DROP,
       DECIDE “x + SUC y - y = SUC x”]
QED

Theorem unpadv_correct:
  env_asm e conf cvs ∧
  i < LENGTH srefs ∧ EL i srefs = W8array ds ∧ LENGTH ds ≠ 0 ∧
  nsLookup e.v (Short "x") = SOME (Loc i) ⇒
  ∃v ck1 ck2.
    evaluate ((s with <| clock := ck1; refs := srefs|>) : unit state) e
             [unpadv_code conf] =
    (s with <| clock := ck2; refs := srefs |>, Rval [v]) ∧
    LIST_TYPE WORD8 (unpad ds) v
Proof
  simp[] >> strip_tac >>
  ‘∃d rest. ds = d::rest’ by (Cases_on ‘ds’ >> gs[]) >> gvs[] >>
  ‘nsLookup e.c conf.cons = SOME (2, TypeStamp "::" list_type_num) ∧
   nsLookup e.c conf.nil = SOME (0, TypeStamp "[]" list_type_num)’
    by gvs[env_asm_def, has_v_def] >>
  simp[evaluate_def, validv_def, do_app_thm, store_lookup_def, GREATER_EQ,
       lit_same_type_def, do_log_def] >>
  reverse $ Cases_on ‘d : word8 = 2w ∨ d = 7w’ >> gns[] >>
  simp[do_if_def, finalv_def]
  >- (simp[evaluate_def, do_app_thm, store_lookup_def, GREATER_EQ,
           lit_same_type_def, do_log_def] >> gs[] >>
      Cases_on ‘d = 6w’
      >- (simp[find_evalform ‘Let _ _ _’, find_evalform ‘App _ _’,
               find_evalform ‘If _ _ _’, find_evalform ‘Log _ _ _’,
               do_app_thm, store_lookup_def, GREATER_EQ,
               do_if_def, terminationTheory.do_eq_def, lit_same_type_def,
               do_log_def] >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ ENV [Letrec find_one _]’ >>
          ‘nsLookup ENV.v (Short "x") = SOME (Loc i)’ by simp[Abbr‘ENV’] >>
          drule_then strip_assume_tac
                     (find_one_equiv |> INST_TYPE [alpha |-> “:unit”]) >>
          gs[store_lookup_def] >>
          pop_assum $ qspec_then ‘s with refs := srefs’ assume_tac >> gs[] >>
          pop_assum $ qspec_then ‘1’ strip_assume_tac >>
          gvs[NUM_def, INT_def] >>
          dxrule evaluate_add_to_clock >> simp[] >> strip_tac >>
          CONV_TAC (pull_namedexvar_conv "ck1") >>
          Q.REFINE_EXISTS_TAC ‘ck1 + ck11’ >> simp[] >>
          simp[do_app_thm, evaluate_def, store_lookup_def, EL_APPEND1,
               lit_same_type_def, opn_lookup_def] >>
          Cases_on ‘hfind_one 1 (6w::rest) = SUC (LENGTH rest)’ >>
          simp[do_if_def]
          >- (simp[evaluate_def, do_con_check_def, build_conv_def,
                   integerTheory.INT_ADD, build_rec_env_def, do_app_thm,
                   do_opapp_def] >>
              irule_at Any EQ_REFL >>
              ‘unpad (6w::rest) = []’ suffices_by
                simp[LIST_TYPE_def, list_type_num_def] >>
              gs[unpad_def, hfind_one_findi, ADD1, AllCaseEqs(),
                 GSYM NOT_MEM_findi_IFF, MIN_DEF] >>
              dsimp[SPLITP_NIL_SND_EVERY, EVERY_MEM]) >>
          simp[evaluate_def, do_app_thm, store_lookup_def, EL_APPEND1,
               opn_lookup_def, build_rec_env_def, do_con_check_def,
               build_conv_def, do_opapp_def] >>
          Q.REFINE_EXISTS_TAC ‘ck11 + 2’>> simp[dec_clock_def] >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ ENV2 [backseg_code _]’ >>
          qspecl_then [‘LENGTH rest’, ‘[]’] mp_tac backseg_correct >>
          simp[LIST_TYPE_def] >> disch_then $ qspec_then ‘ENV2’ mp_tac >>
          simp[Abbr‘ENV2’, list_type_num_def] >> disch_then drule >>
          simp[integerTheory.INT_SUB] >> impl_tac
          >- (‘1 ≤ LENGTH (6w::rest)’ by simp[] >>
              dxrule hfind_one_bound >> simp[]) >>
          strip_tac >> dxrule evaluate_add_to_clock >> simp[] >>
          qmatch_goalsub_rename_tac
            ‘evaluate (s with <| clock := bsck + _; refs := _|>)’ >>
          strip_tac >> Q.REFINE_EXISTS_TAC ‘bsck + ck11’ >> simp[] >>
          irule_at Any EQ_REFL >> pop_assum kall_tac >> pop_assum mp_tac >>
          qmatch_abbrev_tac ‘DATUM l1 resv ⇒ DATUM l2 resv’ >>
          ‘l1 = l2’ suffices_by simp[] >>
          simp[Abbr‘l1’, Abbr‘l2’, unpad_def] >>
          gs[hfind_one_findi, ADD1] >>
          ‘MEM 1w rest’ by metis_tac[NOT_MEM_findi_IFF] >>
          ‘∃px sx. SPLITP ($= 1w) rest = (px,sx)’
            by metis_tac[pair_CASES] >>
          Cases_on ‘sx = []’
          >- gvs[SPLITP_NIL_SND_EVERY, EVERY_MEM] >>
          simp[findi_splitp] >> drule SPLITP_IMP >>
          Cases_on ‘sx’ >> gvs[] >> drule SPLITP_JOIN >> rpt strip_tac >>
          gvs[DECIDE “x + 2 = SUC (SUC x)”, SEG_SUC_CONS, SEG_APPEND2] >>
          simp[ADD1, SEG_LENGTH_ID]) >>
      simp[evaluate_def, do_con_check_def, build_conv_def, unpad_def,
           LIST_TYPE_def, list_type_num_def] >>
      irule_at Any EQ_REFL) >>
  gs[] >> (* 2 equivalent subgoals *)
  simp[evaluate_def, do_app_thm, store_lookup_def, do_log_def, do_if_def,
       lit_same_type_def, opn_lookup_def, integerTheory.INT_ADD, finalv_def,
       integerTheory.INT_SUB, store_alloc_def, EL_APPEND2, EL_APPEND1,
       copy_array_def, store_assign_def, store_v_same_type_def,
       build_rec_env_def, do_con_check_def, build_conv_def, do_opapp_def] >>
  CONV_TAC (pull_namedexvar_conv "ck1") >>
  Q.REFINE_EXISTS_TAC ‘ck11 + 1’ >> simp[dec_clock_def] >>
  CONV_TAC (pull_namedexvar_conv "ck11") >>
  Q.REFINE_EXISTS_TAC ‘ck11 + 1’ >> simp[dec_clock_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ ENV [backseg_code _]’ >>
  qspecl_then [‘LENGTH rest’, ‘[]’] mp_tac backseg_correct >>
  simp[LIST_TYPE_def] >> disch_then $ qspec_then ‘ENV’ mp_tac >>
  simp[Abbr‘ENV’, list_type_num_def] >> disch_then drule >> simp[] >>
  strip_tac >> first_assum $ irule_at Any >>
  gs[CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV SEG_SUC_CONS,unpad_def,
     SEG_LENGTH_ID]
QED

(* Main receiveloop characterisation *)
Theorem env_asm_ignores_append_alist[simp]:
  env_asm (e with v := nsAppend (alist_to_ns al) ns) conf vs ⇔
  env_asm (e with v := ns) conf vs
Proof
  Induct_on ‘al’ >> simp[FORALL_PROD]
QED


Theorem pad_EQ_NIL[simp]:
  pad c l = [] ⇔ F
Proof
  simp[pad_def, AllCaseEqs()]
QED

Definition receive_events_raw_def:
  receive_events_raw conf bufInit src msgChunks =
  let
    data_pairs = ZIP (bufInit::msgChunks,msgChunks)
  in
    MAP (λ(a,b). IO_event "receive" src (ZIP (a,b))) data_pairs
End

Theorem ffi_term_stream_wellformed:
  ∀s. 0 < conf.payload_size ∧ ffi_term_stream conf s src cs ⇒
      cs ≠ [] ∧ (∀e. MEM e cs ⇒ LENGTH e = conf.payload_size + 1) ∧
      final (LAST cs)
Proof
  Induct_on ‘cs’ >> simp[ffi_term_stream_def] >> qx_gen_tac ‘bs’ >>
  qx_gen_tac ‘s’ >>
  Cases_on ‘cs’ >> simp[ffi_term_stream_def]
  >- (Cases_on ‘bs’ >> simp[final_def, pad_def] >> rw[] >>
      gvs[valid_receive_call_format_def, call_FFI_def, AllCaseEqs(), ADD1] >>
      first_x_assum $
        qspec_then ‘GENLIST (K ARB) (conf.payload_size + 1)’ mp_tac >>
      simp[PULL_EXISTS]) >>
  strip_tac >>
  gvs[valid_receive_call_format_def, call_FFI_def, AllCaseEqs(), PULL_EXISTS]>>
  first_x_assum $
        qspec_then ‘GENLIST (K ARB) (conf.payload_size + 1)’ mp_tac >>
  impl_tac >- simp[] >> disch_then $ qx_choose_then ‘ff’ strip_assume_tac >>
  first_x_assum drule >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem do_con_check_NONE[simp]:
  do_con_check e NONE l
Proof
  simp[do_con_check_def]
QED

Theorem build_conv_NONE[simp]:
  build_conv e NONE l = SOME (Conv NONE l)
Proof
  simp[build_conv_def]
QED

Theorem ALL_DISTINCT_receiveloop[simp]:
  ALL_DISTINCT (MAP (λ(f,x,e). f) (receiveloop conf src))
Proof
  simp[receiveloop_def]
QED

val b = receiveloop_def |> concl |> strip_forall |> #2 |> rhs |> lhand
                        |> rand |> rand
Overload receiveloop_body = “λ(conf:config) (src:string). ^b”

Theorem find_recfun_receiveloop[simp]:
  find_recfun "receiveloop" (receiveloop conf src) =
  SOME ("A", receiveloop_body conf src)
Proof
  simp[receiveloop_def]
QED

Theorem nsLookup_build_rec_env_receiveloop[simp]:
  nsLookup (build_rec_env (receiveloop conf src) e ev) (Short nm) =
  if nm = "receiveloop" then
    SOME(Recclosure e (receiveloop conf src) "receiveloop")
  else nsLookup ev (Short nm)
Proof
  Cases_on ‘ev’ >>
  simp[build_rec_env_def, receiveloop_def, nsLookup_def, nsBind_def] >>
  Cases_on ‘nm = "receiveloop"’ >> simp[]
QED

Theorem env_asm_ignores_build_rec_env[simp]:
  env_asm (e with v := build_rec_env f e0 ev) conf vs ⇔
  env_asm (e with v := ev) conf vs
Proof
  simp[build_rec_env_def] >>
  ‘∀g.
     env_asm
       (e with v := FOLDR (λ(h,x,e) env. nsBind h (Recclosure e0 g h) env) ev f)
       conf vs ⇔ env_asm (e with v := ev) conf vs’ suffices_by simp[] >>
  Induct_on ‘f’ >> simp[FORALL_PROD]
QED

(* CORRESPONDENCE RESTRICTIONS *)
(* Payload State and Code Coherence *)
(* -- Check the payload code and state make sense wrt. free variables *)
Definition pFv_def[simp]:
  pFv Nil = {} ∧
  pFv (Send _ fv _ npCd) = fv INSERT pFv npCd ∧
  pFv (Receive _ fv _ npCd) =  pFv npCd DELETE fv ∧
  pFv (IfThen fv npCd1 npCd2) = fv INSERT pFv npCd1 ∪ pFv npCd2 ∧
  pFv (Let bv _ fvs npCd) = (pFv npCd DELETE bv) ∪ set fvs ∧
  pFv (Letrec dv vars e) = set vars ∪ pFv e ∧
  pFv (Fix dv e) = pFv e ∧
  pFv (Call dv) = ∅ ∧
  pFv (FCall dv vars) = set vars
End

Theorem FINITE_pFv[simp]:
  FINITE (pFv e)
Proof
  Induct_on ‘e’ >> simp[]
QED

Theorem pFv_free_var_names_endpoint:
  pFv e = set (free_var_names_endpoint e)
Proof
  Induct_on ‘e’ >> simp[free_var_names_endpoint_def] >>
  simp[EXTENSION, MEM_FILTER] >> metis_tac[]
QED

Theorem pFv_dsubst_E:
  v ∈ pFv (dsubst M dn N) ⇒ v ∈ pFv M ∨ v ∈ pFv N
Proof
  Induct_on ‘M’ >> rw[dsubst_def] >> metis_tac[]
QED

Definition EP_nodenames_def[simp]:
  EP_nodenames Nil = ∅ ∧
  EP_nodenames (Send dest _ _ e) = dest INSERT EP_nodenames e ∧
  EP_nodenames (Receive sender _ _ e) = sender INSERT EP_nodenames e ∧
  EP_nodenames (IfThen _ e1 e2) = EP_nodenames e1 ∪ EP_nodenames e2 ∧
  EP_nodenames (Let _ _ _ e) = EP_nodenames e ∧
  EP_nodenames (Letrec _ _ e) = EP_nodenames e ∧
  EP_nodenames (Fix _ e) = EP_nodenames e ∧
  EP_nodenames (Call _) = ∅ ∧
  EP_nodenames (FCall _ _) = ∅
End

Definition closure_nodenames_def[simp]:
  closure_nodenames (Closure params (funs,bindings) body) =
  EP_nodenames body ∪ LIST_UNION (MAP (closure_nodenames) (MAP SND funs))
Termination
  WF_REL_TAC ‘measure(closure_size)’ >>
  simp[MEM_MAP,PULL_EXISTS] >>
  simp[FORALL_PROD] >> rw[] >>
  drule closure_size_MEM >>
  intLib.COOPER_TAC
End

Definition network_nodenames_def[simp]:
  network_nodenames (NNil) = ∅ ∧
  network_nodenames (NEndpoint p s e) =
  LIST_UNION(MAP (closure_nodenames o SND) s.funs)
   ∪ EP_nodenames e ∧
  network_nodenames (NPar n1 n2) =
  network_nodenames n1 ∪ network_nodenames n2
End

(* TODO: move *)
Theorem MEM_LIST_UNION:
  ∀x l.
  x ∈ LIST_UNION l ⇔
  (∃e. MEM e l ∧ x ∈ e)
Proof
  strip_tac >> Induct >>
  rw[regexpTheory.LIST_UNION_def] >>
  metis_tac[]
QED

Theorem FINITE_EP_nodenames[simp]:
  FINITE (EP_nodenames e)
Proof
  Induct_on ‘e’ >> simp[]
QED

Theorem FINITE_closure_nodenames[simp]:
  FINITE (closure_nodenames c)
Proof
  qid_spec_tac ‘c’ >>
  ho_match_mp_tac closure_nodenames_ind >>
  rw[] >>
  Induct_on ‘funs’ >>
  rw[regexpTheory.LIST_UNION_def]
QED

Theorem FINITE_network_nodenames[simp]:
  FINITE (network_nodenames n)
Proof
  Induct_on ‘n’ >> simp[] >>
  Cases >> simp[] >>
  Induct_on ‘l’ >>
  gvs[regexpTheory.LIST_UNION_def]
QED

Definition wfclosure_def[simp]:
  wfclosure (Closure pms (fs,binds) body :payloadLang$closure) ⇔
    (∀v. v ∈ pFv body ⇒ v ∈ set pms ∪ FDOM binds) ∧
    ∀nm c. MEM (nm,c) fs ⇒ wfclosure c
Termination
  WF_REL_TAC ‘measure closure_size’ >> rpt gen_tac >> Induct_on ‘fs’ >>
  simp[FORALL_PROD, closure_size_def] >> rw[] >> simp[] >>
  first_x_assum (drule_then assume_tac) >> simp[] >>
  irule LESS_LESS_EQ_TRANS >> first_x_assum (irule_at Any) >> simp[]
End

Definition pSt_pCd_corr_def:
  pSt_pCd_corr conf (pSt :payloadLang$closure payloadLang$state) pCd ⇔
    (∀vn. vn ∈ pFv pCd ⇒ ∃vv. FLOOKUP pSt.bindings vn = SOME vv) ∧
    (∀nm c. MEM (nm,c) pSt.funs ⇒ wfclosure c) ∧
    (∀k d ds. FLOOKUP pSt.queues k = SOME ds ∧ MEM d ds ⇒
              LENGTH d = conf.payload_size + 1)
End

Theorem pSt_pCd_corr_alt:
  pSt_pCd_corr conf pst pcd ⇔
    (∀v. v ∈ pFv pcd ⇒ v ∈ FDOM pst.bindings) ∧
    (∀nm c. MEM (nm,c) pst.funs ⇒ wfclosure c) ∧
    (∀k d ds. FLOOKUP pst.queues k = SOME ds ∧ MEM d ds ⇒
              LENGTH d = conf.payload_size + 1)
Proof
  simp[pSt_pCd_corr_def, FLOOKUP_DEF]
QED

(* Payload State and Semantic Environment *)
(* -- Check the semantic environment contains all the variable bindings in
      the payload state and also matches all the config assumptions        *)
Definition sem_env_cor_def:
  sem_env_cor conf (pSt :closure payloadLang$state) cEnv vs ⇔
    env_asm cEnv conf vs ∧
    ∀ n v. FLOOKUP pSt.bindings n = SOME v ⇒
           ∃v'. nsLookup cEnv.v (Short (ps2cs n)) = SOME v' ∧
                DATUM v v'
End

(* -- Check the semantic environment has all the Let functions
      defined as specified in given list *)
Definition enc1_ok_def:
  enc1_ok conf cEnv f n ⇔
    ∃cl.
      SOME cl = nsLookup cEnv.v (getLetID conf n) ∧
      (LIST_TYPE DATUM --> DATUM) f cl
End

Definition enc_ok_def:
    (enc_ok _ _ [] [] = T) ∧
    (enc_ok conf cEnv (f::fs) (n::ns) ⇔
       (∃cl.
          SOME cl = nsLookup cEnv.v (getLetID conf n) ∧
          (LIST_TYPE DATUM --> DATUM) f cl
       ) ∧
       enc_ok conf cEnv fs ns
    ) ∧
    (enc_ok _ _ _ _ = F)
End

Theorem enc_ok_LIST_REL:
  enc_ok conf cEnv = LIST_REL (enc1_ok conf cEnv)
Proof
  simp[FUN_EQ_THM] >> Induct >> simp[enc_ok_def, LIST_REL_def]
  >- (Cases >> simp[enc_ok_def]) >>
  gen_tac >> Cases >> simp[enc_ok_def, enc1_ok_def]
QED

(* -- Helper Theorems about enc_ok *)
Theorem enc_ok_take:
  ∀conf cEnv x y vs.
    enc_ok conf cEnv (x ++ y) vs ⇒
    enc_ok conf cEnv x (TAKE (LENGTH x) vs)
Proof
  rw[enc_ok_LIST_REL, LIST_REL_SPLIT1] >>
  rename [‘LIST_REL _ x (TAKE _ (ys ++ zs))’] >>
  ‘LENGTH ys = LENGTH x’ by metis_tac[LIST_REL_LENGTH] >>
  simp[TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]
QED

Theorem enc_ok_drop:
  ∀conf cEnv x y vs.
    enc_ok conf cEnv (x ++ y) vs ⇒
    enc_ok conf cEnv y (DROP (LENGTH x) vs)
Proof
  rw[enc_ok_LIST_REL, LIST_REL_SPLIT1] >>
  rename [‘LIST_REL _ y (DROP (LENGTH x) (ys ++ zs))’] >>
  ‘LENGTH ys = LENGTH x’ by metis_tac[LIST_REL_LENGTH] >>
  simp[DROP_APPEND2]
QED

Theorem enc_ok_bind[simp]:
  ∀conf cEnv hs vs k val ns.
    enc_ok conf (cEnv with v := nsBind k val ns) hs vs ⇔
    enc_ok conf (cEnv with v := ns) hs vs
Proof
  Induct_on ‘hs’ >>
  rw[] >> Cases_on ‘vs’ >> gs[enc_ok_def, getLetID_def]
QED


(* FFI and Payload State *)
(* -- Check identifier and FFI model contains
      correct messages *)

Definition ffi_state_cor_def:
  ffi_state_cor conf cpNum pSt pN (fNum,fQueue,fNet) ⇔
    cpNum = fNum ∧
    ffi_eq conf (fNum, fQueue, fNet) (fNum, pSt.queues, pN) ∧
    ffi_wf (fNum, pSt.queues, pN)
End

Theorem ffi_state_cor_thm:
  ffi_state_cor conf cpNum pSt pN ffi ⇔
  cpNum = FST ffi ∧
  ffi_eq conf ffi (FST ffi, pSt.queues,pN) ∧
  ffi_wf (FST ffi, pSt.queues,pN)
Proof
  PairCases_on ‘ffi’ >> simp[ffi_state_cor_def]
QED

Theorem ffi_state_cor_ignores_funs[simp]:
  ffi_state_cor conf cpNum (pst with funs := fv) pN ffis ⇔
  ffi_state_cor conf cpNum pst pN ffis
Proof
  PairCases_on ‘ffis’ >> simp[ffi_state_cor_def]
QED

Theorem ffi_state_cor_ignores_bindings[simp]:
  ffi_state_cor c p (ps with bindings := v) pN ffi ⇔
  ffi_state_cor c p ps pN ffi
Proof
  PairCases_on ‘ffi’ >> simp[ffi_state_cor_def]
QED

Definition closure_cpEval_valid_def:
  closure_cpEval_valid conf cEnv0 cvs dn (Closure params (funs,bindings) e) =
  ∃cEnv0' vs'.
    ALL_DISTINCT params ∧
    env_asm cEnv0' conf cvs ∧
    enc_ok conf cEnv0' (letfuns e) vs' ∧
    (∀n v.
       FLOOKUP bindings n = SOME v ⇒
       ∃v'. nsLookup cEnv0'.v (Short (ps2cs n)) = SOME v' ∧ DATUM v v') ∧
    (∀vn. vn ∈ pFv e ⇒ IS_SOME (FLOOKUP bindings vn)) ∧
    nsLookup cEnv0.v (Short (ps2cs2 dn)) =
    SOME (Recclosure cEnv0'
          [(ps2cs2 dn,"",
            Mat (𝕍 "")
                [(Pcon NONE (MAP (Pvar o ps2cs) params), compile_endpoint conf vs' e)])]
          (ps2cs2 dn)) ∧
    (∀dn cl. ALOOKUP funs dn = SOME cl ⇒
          closure_cpEval_valid conf cEnv0' cvs dn cl)
Termination
  WF_REL_TAC ‘measure (closure_size o SND o SND o SND o SND)’>>
  rpt gen_tac >> Induct_on ‘funs’ >>
  simp[FORALL_PROD, closure_size_def] >> rw[] >> simp[] >>
  first_x_assum (drule_then assume_tac) >> simp[] >>
  irule LESS_LESS_EQ_TRANS >> first_x_assum (irule_at Any) >> simp[]
End

Definition funs_cpEval_valid_def:
  funs_cpEval_valid conf cEnv0 cvs funs =
  ∀dn cl. ALOOKUP funs dn = SOME cl ⇒
          closure_cpEval_valid conf cEnv0 cvs dn cl
End

(* Combined *)
Definition cpEval_valid_def:
  cpEval_valid conf cpNum cEnv pSt pCd pN vs cvs cSt ⇔
    conf.payload_size ≠ 0 ∧
    env_asm cEnv conf cvs ∧
    funs_cpEval_valid conf cEnv cvs pSt.funs ∧
    enc_ok conf cEnv (letfuns pCd) vs ∧
    pSt_pCd_corr conf pSt pCd ∧
    sem_env_cor conf pSt cEnv cvs ∧
    ffi_state_cor conf cpNum pSt pN cSt.ffi.ffi_state ∧
    ffi_wf cSt.ffi.ffi_state ∧
    cSt.ffi.oracle = comms_ffi_oracle conf ∧
    normalised pSt.queues
End
Overload simR[local] = “cpEval_valid”

(* VALIDITY *)
(* Check that Payload States with label transition and
   two corresponding FFI states are all valid to produce
   coherent corresponding transitions *)
Definition cpFFI_valid_def:
  (cpFFI_valid conf pSt1 pSt2 ffi1 ffi2 (payloadSem$LSend _ d rp)
    ⇔ strans conf ffi1 (ASend rp d) ffi2) ∧
  (cpFFI_valid conf pSt1 pSt2 ffi1 ffi2 (LReceive _ _ _)
    ⇔ ffi_eq conf ffi1 ffi2) ∧
  (cpFFI_valid conf pSt1 pSt2 ffi1 ffi2 LTau
    ⇔ case (some (sp,d).
              pSt1.queues = normalise_queues (pSt2.queues |+ (sp,d::qlk pSt2.queues sp))) of
        SOME (sp,d) => strans conf ffi1 (ARecv sp d) ffi2
      | NONE        => ffi_eq conf ffi1 ffi2)
End

Theorem FDOM_normalise_queues:
  FDOM (normalise_queues fm) = FDOM fm DIFF { k | k ∈ FDOM fm ∧ fm ' k = []}
Proof
  simp[normalise_queues_def, DRESTRICT_DEF] >>
  csimp[EXTENSION, FLOOKUP_DEF]
QED

Theorem FAPPLY_normalise_queues:
  normalise_queues fm ' k = if k ∈ FDOM fm ∧ fm ' k ≠ [] then fm ' k
                            else FEMPTY ' k
Proof
  csimp[normalise_queues_def, DRESTRICT_DEF, FLOOKUP_DEF]
QED

Theorem normalise_queues_dequeue_eq:
  ∀s s' q r.
    normalised s'.queues ∧
    s.queues = normalise_queues (s'.queues |+ (q,r::qlk s'.queues q))
    ⇒ s'.queues = normalise_queues (s.queues |+ (q,qlk s'.queues q))
Proof
  rw [] \\ fs [normalised_def]
  \\ Cases_on ‘qlk s'.queues q’
  >- (fs [qlk_def,fget_def]
      \\ EVERY_CASE_TAC
      >- (fs [normalise_queues_FUPDATE_NONEMPTY,FLOOKUP_DEF]
          \\ drule NOT_FDOM_DRESTRICT \\ rw [])
      \\ fs [] \\ rveq
      \\ pop_assum (fn t1 => last_assum (fn t2 => assume_tac (ONCE_REWRITE_RULE [GSYM t2] t1)))
      \\ fs [normalise_queues_def,FLOOKUP_DRESTRICT] \\ fs [])
  \\ qmatch_goalsub_abbrev_tac ‘_ = ss’
  \\ qpat_assum ‘normalise_queues _ = _’  (ONCE_REWRITE_TAC o single o GSYM)
  \\ UNABBREV_ALL_TAC
  \\ AP_TERM_TAC
  \\ ONCE_REWRITE_TAC [GSYM fmap_EQ_THM]
  \\ fs [qlk_def,fget_def]
  \\ EVERY_CASE_TAC
  \\ fs [] \\ rveq \\ rw []
  >- fs [FLOOKUP_DEF,ABSORPTION_RWT]
  \\ rw [FAPPLY_FUPDATE_THM]
  \\ fs [FLOOKUP_DEF]
QED

Overload smSt[local] = “bigSmallEquiv$to_small_st”
Overload smEv[local] = “smallStep$small_eval”
Overload stepr[local] = “smallStep$e_step_reln”
Theorem pSt_pCd_corr_Send:
  pSt_pCd_corr conf pst (Send p v n e) ⇔
    (∃vv. FLOOKUP pst.bindings v = SOME vv) ∧ pSt_pCd_corr conf pst e
Proof
  simp[pSt_pCd_corr_def, DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

Theorem cpEval_valid_Send:
  cpEval_valid conf p1 env pst (Send p2 v n e) pN vs cvs cst ⇔
    cpEval_valid conf p1 env pst e pN vs cvs cst ∧
    (∃vv. FLOOKUP pst.bindings v = SOME vv)
Proof
  simp[cpEval_valid_def, EQ_IMP_THM, letfuns_def, pSt_pCd_corr_Send]
QED

Theorem cpEval_nsLookup_PLbindings:
  cpEval_valid conf p cEnv pSt e pN vs cvs cSt ∧
  FLOOKUP pSt.bindings v = SOME d ⇒
  ∃dd. nsLookup cEnv.v (Short (ps2cs v)) = SOME dd ∧ DATUM d dd
Proof
  simp[cpEval_valid_def, pSt_pCd_corr_def, sem_env_cor_def] >> rw[]
QED

Theorem nsLookup_build_rec_env_sendloop =
  (SIMP_CONV (srw_ss()) [build_rec_env_def, sendloop_def] THENC
   SIMP_CONV (srw_ss()) [GSYM sendloop_def])
  “nsLookup (build_rec_env (sendloop conf data) env v) (Short "sendloop")”;

Theorem final_padNIL[simp]:
  conf.payload_size ≠ 0 ⇒ final (pad conf [])
Proof
  simp[pad_def, final_def]
QED

Theorem update_state_ffi_has_node[simp]:
  ∀st. ffi_has_node dest st ∧ dest ≠ FST st ⇒
       (ffi_has_node nd
        (update_state st (comms_ffi_oracle conf)
         (send_events conf (MAP (n2w o ORD) dest) data)) =
        ffi_has_node nd st)
Proof
  simp[send_events_def] >> completeInduct_on ‘LENGTH data’ >>
  Cases >> simp[update_state_def, Once compile_message_def] >>
  rw[update_state_def, comms_ffi_oracle_def, ffi_send_def, pad_LENGTH] >>
  simp[AllCaseEqs(), MAP_MAP_o, CHR_w2n_n2w_ORD]
  >- (SELECT_ELIM_TAC >> conj_tac >>
      DEEP_INTRO_TAC optionTheory.some_intro >> simp[]
      >- (‘valid_send_dest (MAP (n2w o ORD) dest) st’
            by simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
          drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      metis_tac[strans_pres_nodes])
  >- (SELECT_ELIM_TAC >> conj_tac >>
      DEEP_INTRO_TAC optionTheory.some_intro >> simp[]
      >- (‘valid_send_dest (MAP (n2w o ORD) dest) st’
            by simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
          drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      metis_tac[strans_pres_nodes]) >>
  gs[PULL_FORALL] >>
  first_x_assum (qspec_then ‘DROP (conf.payload_size - 1) t’ mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_abbrev_tac ‘ffi_has_node nd (update_state ST _ _) = _’ >>
  first_x_assum (qspec_then ‘ST’ mp_tac) >>
  impl_tac
  >- (simp[Abbr‘ST’] >> SELECT_ELIM_TAC >> conj_tac >>
      DEEP_INTRO_TAC optionTheory.some_intro >> simp[]
      >- (‘valid_send_dest (MAP (n2w o ORD) dest) st’
            by simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
          drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      metis_tac[strans_pres_pnum, strans_pres_nodes]) >> simp[] >>
  disch_then kall_tac >> simp[Abbr‘ST’] >>
  SELECT_ELIM_TAC >> conj_tac >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp[]
  >- (‘valid_send_dest (MAP (n2w o ORD) dest) st’
        by simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
      drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
  metis_tac[strans_pres_pnum, strans_pres_nodes]
QED

Theorem update_state_ffi_wf[simp]:
  ∀st dest. ffi_has_node dest st ∧ dest ≠ FST st ⇒
            (ffi_wf (update_state st (comms_ffi_oracle conf)
                     (send_events conf (MAP (n2w o ORD) dest) data)) =
             ffi_wf st)
Proof
  simp[send_events_def] >> completeInduct_on ‘LENGTH data’ >>
  Cases >> simp[update_state_def, Once compile_message_def] >>
  rw[update_state_def, comms_ffi_oracle_def, ffi_send_def, pad_LENGTH] >>
  ‘valid_send_dest (MAP (n2w o ORD) dest) st’
    by simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
  simp[AllCaseEqs(), MAP_MAP_o, CHR_w2n_n2w_ORD]
  >- (SELECT_ELIM_TAC >> conj_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
      simp[]
      >- (drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      metis_tac[strans_pres_wf])
  >- (SELECT_ELIM_TAC >> conj_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
      simp[]
      >- (drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      metis_tac[strans_pres_wf]) >>
  gs[PULL_FORALL] >>
  qmatch_abbrev_tac ‘ffi_wf (update_state ST _ _) = _’ >>
  first_x_assum $
    qspecl_then [‘DROP (conf.payload_size - 1) t’, ‘ST’, ‘dest’] mp_tac >>
  simp[] >> impl_tac
  >- (simp[Abbr‘ST’] >>
      SELECT_ELIM_TAC >> conj_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
      simp[]
      >- (drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      metis_tac[strans_pres_nodes, strans_pres_pnum]) >>
  disch_then SUBST_ALL_TAC >> simp[Abbr‘ST’] >>
  SELECT_ELIM_TAC >> conj_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
  simp[]
  >- (drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
  metis_tac[strans_pres_wf]
QED

Theorem ffi_eq_simulationL:
  ffi_eq conf (pn,Q0a,N0a) (pn,Q0b,N0b) ∧
  strans conf (pn,Q0a,N0a) L (pn,Qa,Na) ⇒
  ∃Qb Nb. strans conf (pn,Q0b,N0b) L (pn,Qb,Nb) ∧
          ffi_eq conf (pn,Qa,Na) (pn,Qb,Nb)
Proof
  simp[ffi_eq_def] >> strip_tac >>
  drule_all (bisimulationTheory.BISIM_REL_cases |> iffLR |> cj 1) >>
  simp[EXISTS_PROD] >> metis_tac[strans_pres_pnum, FST]
QED

Theorem trans_receptive:
  net_has_node N0 dst ∧ dst ≠ src ⇒
  ∃N. trans conf N0 (LReceive src msg dst) N ∧
      net_has_node N = net_has_node N0 ∧ net_wf N = net_wf N0
Proof
  Induct_on ‘N0’ >> simp[net_has_node_def, FUN_EQ_THM, net_wf_def] >>
  metis_tac[trans_rules, net_has_node_def, net_wf_def]
QED

Theorem trans_receive_has_node:
  ∀N0 N.
    trans conf N0 (LReceive src m dst) N ⇒
    net_has_node N0 dst ∧ net_has_node N dst
Proof
  Induct_on ‘trans’ >> simp[net_has_node_def]
QED

Theorem strans_send_has_node:
  ∀q0 N0 q N.
    strans conf (pnum,q0,N0) (ASend dest m) (pnum,q,N) ⇒
    net_has_node N0 dest ∧ net_has_node N dest
Proof
  Induct_on ‘strans’ >> simp[] >>
  metis_tac[trans_receive_has_node, trans_pres_nodes]
QED

Theorem strans_send_hold_queues_constant:
  ∀pnum q N0 dst m.
    net_has_node N0 dst ∧ dst ≠ pnum ⇒
    ∃N1. strans conf (pnum,q,N0) (ASend dst m) (pnum,q,N1) ∧
         net_has_node N1 = net_has_node N0 ∧ net_wf N1 = net_wf N0
Proof
  metis_tac[trans_receptive, strans_rules]
QED

Theorem match_send_hold_queues_ffi_eq:
  ffi_eq conf (p,qA,NA) (p,qB,NB) ∧
  ffi_wf (p,qA,NA) ∧ ffi_wf (p,qB,NB) ∧
  strans conf (p,qA,NA) (ASend dst msg) (p,qA',NA') ⇒
  ∃NB'. ffi_eq conf (p,qA',NA') (p,qB,NB') ∧ ffi_wf (p,qB,NB')
Proof
  strip_tac >> irule_at Any ffi_eq_pres >>
  first_assum (irule_at (Pat ‘ffi_eq _ _’)) >> simp[] >>
  first_assum (irule_at Any) >> gs[ffi_wf_def] >>
  dxrule_all_then strip_assume_tac ffi_eq_simulationL >>
  drule_then strip_assume_tac strans_send_has_node >>
  metis_tac [strans_send_hold_queues_constant]
QED

Theorem update_state_send_ffi_state_cor:
  ∀ffst dest pN.
    ffi_has_node dest ffst ∧ dest ≠ FST ffst ∧ ffi_wf ffst ∧
    ffi_state_cor conf src pSt pN ffst ⇒
    ∃pN'.
      ffi_state_cor conf src pSt pN'
                    (update_state ffst (comms_ffi_oracle conf)
                     (send_events conf (MAP (n2w o ORD) dest) data))
Proof
  simp[send_events_def] >> completeInduct_on ‘LENGTH data’ >>
  Cases >> simp[update_state_def, Once compile_message_def] >>
  rw[update_state_def, comms_ffi_oracle_def, ffi_send_def, pad_LENGTH] >>
  ‘valid_send_dest (MAP (n2w o ORD) dest) ffst’
    by simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
  simp[AllCaseEqs(), MAP_MAP_o, CHR_w2n_n2w_ORD]
  >- (SELECT_ELIM_TAC >> conj_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
      simp[]
      >- (drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      simp[FORALL_PROD] >> PairCases_on ‘ffst’ >>
      gvs[ffi_state_cor_def] >> rpt strip_tac >>
      drule strans_pres_pnum >> simp[] >> rw[] >>
      metis_tac[match_send_hold_queues_ffi_eq])
  >- (SELECT_ELIM_TAC >> conj_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
      simp[]
      >- (drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
      simp[FORALL_PROD] >> PairCases_on ‘ffst’ >>
      gvs[ffi_state_cor_def] >> rpt strip_tac >>
      drule strans_pres_pnum >> simp[] >> rw[] >>
      metis_tac[match_send_hold_queues_ffi_eq]) >>
  gs[PULL_FORALL] >>
  first_x_assum irule >> simp[] >>
  SELECT_ELIM_TAC >> conj_tac >> DEEP_INTRO_TAC optionTheory.some_intro >>
  simp[]
  >- (drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
  simp[FORALL_PROD] >> rw[]
  >- (drule_all strans_pres_wf >> simp[ffi_wf_def])
  >- metis_tac[strans_pres_pnum, FST]
  >- metis_tac[strans_pres_nodes] >>
  PairCases_on ‘ffst’ >> gvs[ffi_state_cor_def] >>
  drule_then assume_tac strans_pres_pnum >> gvs[] >>
  metis_tac[match_send_hold_queues_ffi_eq]
QED

Theorem find_recfun_sendloop[simp]:
  find_recfun "sendloop" (sendloop conf dest) =
  SOME ("x", sendloop_code conf dest)
Proof
  simp[sendloop_def, Once find_recfun_def]
QED

Theorem store_v_same_type_refl[simp]:
   store_v_same_type v v
Proof
  Cases_on ‘v’ >> simp[store_v_same_type_def]
QED

Theorem store_assign_lookup_nochange[simp]:
  store_lookup loc refs = SOME v ⇒ store_assign loc v refs = SOME refs
Proof
  simp[store_lookup_def, store_assign_def] >> rw[]>>
  simp[LUPDATE_SAME]
QED

Theorem RTC_stepr_evaluateL:
  (∀(s00:α state).
     evaluate (s00 with clock := ckf1 s00) env [e] =
     (s00 with <| clock := ckf2 s00; refs := s00.refs ++ rfn s00|>,
      Rval [vfn s00])) ∧
  smallStep$continue (smSt (s00 with refs := s00.refs ++ rfn s00))
                     (vfn s00) cs =
  smallStep$Estep a ∧ stepr꙳ a b ⇒
  stepr꙳ (env,smSt s00,Exp e,cs) b
Proof
  strip_tac >> irule (iffRL RTC_CASES_RTC_TWICE) >>
  irule_at (Pos hd) smallstep_drop_conts >>
  strip_assume_tac
           (small_eval_def |> cj 1 |> iffLR |> GEN_ALL
            |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
            |> INST_TYPE [“:'ffi” |-> alpha]) >>
  pop_assum (irule_at (Pos hd)) >>
  irule_at (Pos hd) (small_big_exp_equiv |> iffRL |> cj 1) >>
  irule_at Any (iffRL bigClockTheory.big_clocked_unclocked_equiv) >>
  simp[funBigStepEquivTheory.functional_evaluate] >>
  first_x_assum (C (resolve_then Any mp_tac) evaluate_set_clock) >>
  simp[SKOLEM_THM] >>
  disch_then (qx_choose_then ‘ckf’ (irule_at (Pos hd))) >> simp[] >>
  irule (cj 2 RTC_RULES) >> simp[e_step_reln_def, e_step_def]
QED

Theorem state_cases:
  ∀s. ∃c r f nts nes.
        s = <| clock := c; refs := r; ffi := f; next_type_stamp := nts;
               next_exn_stamp := nes |>
Proof
  simp[FORALL_state, state_component_equality]
QED

Theorem FORALL_state = FORALL_state |> INST_TYPE [“:'ffi0” |-> alpha,
                                                  “:'ffi” |-> alpha]

Theorem RTC_stepr_fixedstate_evaluateL0:
  evaluate ((s00 with <| clock := clk1; refs := refs00 |>) : α state) env [e] =
  (s00 with <| clock := clk2; refs := refs01|>, Rval [rval]) ∧
  smallStep$continue (refs01, ffi00) rval cs =
  smallStep$Estep a ∧ stepr꙳ a b ⇒
  stepr꙳ (env,(refs00,ffi00 : α ffi_state),Exp e,cs) b
Proof
  strip_tac >> irule (iffRL RTC_CASES_RTC_TWICE) >>
  irule_at (Pos hd) smallstep_drop_conts >>
  strip_assume_tac
           (small_eval_def |> cj 1 |> iffLR |> GEN_ALL
            |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
            |> INST_TYPE [“:'ffi” |-> alpha]) >>
  pop_assum (irule_at (Pos hd)) >>
  irule_at (Pos hd)
           (small_big_exp_equiv |> iffRL
                                |> cj 1
                                |> SRULE [FORALL_state, to_small_st_def]) >>
  irule_at Any (iffRL bigClockTheory.big_clocked_unclocked_equiv) >>
  simp[funBigStepEquivTheory.functional_evaluate] >>
  first_x_assum (C (resolve_then Any mp_tac) evaluate_set_clock) >>
  simp[SKOLEM_THM] >> disch_then $ qx_choose_then ‘ckf’ assume_tac >>
  irule_at (Pos hd)
           (evaluate_ffi_intro' |> SRULE [FORALL_state]
                                |> INST_TYPE [alpha |-> beta]) >>
  Cases_on ‘s00’ using state_cases >> gs[] >> first_assum $ irule_at Any >>
  irule (cj 2 RTC_RULES) >> simp[e_step_reln_def, e_step_def]
QED

Theorem RTC_stepr_fixedstate_evaluateL =
        RTC_stepr_fixedstate_evaluateL0
          |> Q.INST [‘b’ |-> ‘a’, ‘refs01’ |-> ‘refs00 ++ newrefs’]
          |> SRULE []

Theorem RTC_stepr_changerefs_evaluateL =
        RTC_stepr_fixedstate_evaluateL0 |> Q.INST [‘b’ |-> ‘a’] |> SRULE []

Theorem ps2cs_neqxy[simp]:
  ps2cs v ≠ "x" ∧ ps2cs v ≠ "y"
Proof
  simp[ps2cs_def]
QED

Theorem send_invariant_arg3eq:
  ∀conf l x. x = comms_ffi_oracle conf ⇒
             ffi_accepts_rel (valid_send_dest l)
                             (valid_send_call_format conf l)
                             x
Proof
  simp[send_invariant]
QED

fun atlast f []= raise Fail "atlast.empty"
| atlast f [x] = [f x]
| atlast f (h::t) = h :: atlast f t

Theorem pat_bindings' =
  astTheory.pat_bindings_def
    |> CONV_RULE (EVERY_CONJ_CONV (pull_namedallvar_conv "already_bound"))
    |> CONJUNCTS
    |> map (Q.SPEC ‘[]’)
    |> atlast $ CONV_RULE $ STRIP_QUANT_CONV $ RAND_CONV $
         REWR_CONV $ CONJUNCT2 $
         semanticPrimitivesPropsTheory.pat_bindings_accum
    |> LIST_CONJ

Theorem pat_bindings_MAP_Pvar[simp]:
  pats_bindings (MAP (Pvar o f) l) A = MAP f (REVERSE l) ++ A
Proof
  ONCE_REWRITE_TAC [semanticPrimitivesPropsTheory.pat_bindings_accum] >>
  simp[] >>
  Induct_on ‘l’ >> simp[pat_bindings']
QED

Theorem pmatch_tuple_MAP_Pvar:
  ALL_DISTINCT (MAP f vars) ⇒
  ∀A. pmatch_list cs refs (MAP (Pvar o f) vars) (MAP vf vars) A =
      Match (REVERSE (MAP (λv. (f v, vf v)) vars) ++ A)
Proof
  Induct_on ‘vars’ >> simp[terminationTheory.pmatch_def]
QED

Theorem enc_ok_nsAppend_alist[simp]:
  ∀al.
    enc_ok conf (E with v := nsAppend (alist_to_ns al) ns) fs vs ⇔
      enc_ok conf (E with v := ns) fs vs
Proof
  Induct >> simp[enc_ok_def, FORALL_PROD]
QED

Theorem enc_ok_build_rec_env[simp]:
  enc_ok conf (E with v := build_rec_env cls E' ns) fs vs ⇔
    enc_ok conf (E with v := ns) fs vs
Proof
  simp[build_rec_env_def] >>
  qpat_abbrev_tac ‘X = Recclosure E' cls’ >> RM_ABBREV_TAC "X" >>
  Induct_on ‘cls’ >> simp[FORALL_PROD]
QED

Theorem evaluate_ffi_intro'':
  evaluate s env e = (s',r) ∧ s'.ffi = s.ffi ∧
  (∀outcome. r ≠ Rerr (Rabort (Rffi_error outcome))) ∧ t.refs = s.refs ∧
  t.clock = s.clock ∧ t' = t with <| refs := s'.refs; clock := s'.clock |> ⇒
  evaluate t env e = (t',r)
Proof
  strip_tac >> drule evaluate_ffi_intro' >> simp[] >>
  qpat_x_assum ‘t.clock = s.clock’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘t.refs = s.refs’ (SUBST_ALL_TAC o SYM) >>
  disch_then $ qspec_then ‘t’ mp_tac >> simp[]
QED

Theorem RTC_stepr_evaluateL':
  (∀s00:α semanticPrimitives$state. eval_rel s00 env exp s00 (vfn s00.refs)) ∧
  smallStep$continue (refs0, ffi0) (vfn refs0) cs = smallStep$Estep a ∧
  stepr꙳ a b ⇒
  stepr꙳ (env,(refs0,ffi0 : α ffi_state),Exp exp,cs) b
Proof
  strip_tac >> irule (iffRL RTC_CASES_RTC_TWICE) >>
  irule_at (Pos hd) smallstep_drop_conts  >>
  strip_assume_tac
           (small_eval_def |> cj 1 |> iffLR |> GEN_ALL
            |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
            |> INST_TYPE [“:'ffi” |-> alpha]) >>
  pop_assum (irule_at (Pos hd)) >> gs[eval_rel_def] >>
  qabbrev_tac ‘st0 = ARB with <| refs := refs0; ffi := ffi0 |>’ >>
  ‘(refs0,ffi0) = smSt st0’ by simp[to_small_st_def, Abbr‘st0’] >> simp[] >>
  irule_at (Pos hd) (small_big_exp_equiv |> iffRL |> cj 1) >>
  irule_at Any (iffRL bigClockTheory.big_clocked_unclocked_equiv) >>
  simp[funBigStepEquivTheory.functional_evaluate] >>
  gs[SKOLEM_THM] >>
  first_x_assum (C (resolve_then Any mp_tac) evaluate_set_clock) >>
  simp[SKOLEM_THM] >>
  disch_then (qx_choose_then ‘ckf’ strip_assume_tac) >>
  first_assum (irule_at (Pos hd)) >> simp[] >>
  irule (cj 2 RTC_RULES) >> simp[e_step_reln_def, e_step_def] >>
  gvs[to_small_st_def]
QED

Theorem eval_rel_intro_ffi:
  (∀refs.
     eval_rel (empty_state with refs := refs) env exp
              (empty_state with refs := refs) v) ⇒
  ∀vfn. (∀s00. eval_rel s00 env exp s00 (vfn s00.refs)) ⇔ vfn = K v
Proof
  simp[eval_rel_def, EQ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  pop_assum (strip_assume_tac o SRULE [SKOLEM_THM]) >>
  assume_tac
    (evaluate_ffi_intro' |> INST_TYPE [beta |-> alpha, alpha |-> “:unit”])>>
      first_assum (pop_assum o resolve_then (Pos hd) mp_tac) >> simp[] >>
  reverse (rpt strip_tac)
  >- (pop_assum $ qspecl_then [‘s00’, ‘s00.refs’] mp_tac >> simp[]) >>
  pop_assum (strip_assume_tac o SRULE [SKOLEM_THM]) >>
  first_x_assum (qspecl_then [‘t’, ‘t.refs’] (strip_assume_tac o SRULE [] o
                                              Q.GEN ‘t’)) >>
  pop_assum (C (resolve_then (Pos hd) mp_tac) evaluate_add_to_clock) >> simp[]>>
  pop_assum (C (resolve_then (Pos hd) mp_tac) evaluate_add_to_clock) >> simp[]>>
  rename [‘_ with clock := _ + f (_ : α semanticPrimitives$state)’,
          ‘_ with clock := _ + g (_.refs)’] >>
  rpt strip_tac >>
  qpat_x_assum ‘∀t ex. evaluate (t with clock := _ + g t.refs) _ _ = _’ $
               qspecl_then [‘s’, ‘f s’] (mp_tac o Q.GEN ‘s’) >>
  first_x_assum $ qspecl_then [‘s’, ‘g s.refs’] (assume_tac o Q.GEN ‘s’) >>
  gs[] >> simp[FUN_EQ_THM] >> strip_tac >> qx_gen_tac ‘rfs’ >>
  pop_assum $ qspec_then ‘ARB with refs := rfs’ mp_tac >> simp[]
QED

Theorem states_with_clocks_EQ[simp]:
  s with clock := x = s with clock := y ⇔ x = y
Proof
  simp[state_component_equality]
QED

Theorem Pstrefs[simp]:
  (∀s. P s.refs) <=> (∀rfs. P rfs)
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  pop_assum $ qspec_then ‘ARB with refs := rfs’ mp_tac >> simp[]
QED

Theorem EXstrefsffi:
  (∃s. P s.refs s.ffi) ⇔ (∃refs ffi. P refs ffi)
Proof
  simp[EQ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  qexists_tac ‘ARB with <| refs := refs; ffi := ffi|>’ >> simp[]
QED

Theorem FAstrefsffi:
  (∀s. P s.refs s.ffi) ⇔ ∀refs ffi. P refs ffi
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  pop_assum $ qspec_then ‘ARB with <| refs := refs; ffi := ffi|>’ mp_tac >>
  simp[]
QED

Theorem WORD8_11:
  ∀b v1 v2. WORD8 b v1 ∧ WORD8 b v2 ⇒ v1 = v2
Proof
  simp[WORD_def]
QED

Theorem DATUM_11:
  ∀x v1 v2. DATUM x v1 ∧ DATUM x v2 ⇒ v1 = v2
Proof
  Induct_on ‘x’ >> simp[LIST_TYPE_def] >> rw[] >> metis_tac[WORD8_11]
QED

Theorem ORD_MOD256[simp]:
  ORD c MOD 256 = ORD c
Proof
  simp[X_MOD_Y_EQ_X, ORD_BOUND]
QED

Theorem finalv_correct:
  nsLookup e.v (Short bnm) = SOME (Loc i) ∧ i < LENGTH s.refs ∧ msg ≠ [] ∧
  store_lookup i s.refs = SOME (W8array msg) ⇒
  evaluate s e [finalv bnm] = (s, Rval [Boolv (final msg)])
Proof
  Cases_on ‘msg’ >>
  simp[evaluate_def, finalv_def, do_app_thm, GREATER_EQ, lit_same_type_def,
       do_log_def, final_def] >>
  Cases_on ‘h = 7w’ >>
  simp[evaluate_def, do_app_thm, lit_same_type_def] >> metis_tac[]
QED

Theorem convDatum_correct:
  env_asm e conf vs ⇒
  ∃v. evaluate s e [convDatum conf h] = (s, Rval [v]) ∧
      LIST_TYPE WORD8 h v
Proof
  simp[env_asm_def, has_v_def] >> strip_tac >> Induct_on ‘h’ >>
  simp[evaluate_def, convDatum_def, do_con_check_def,
       build_conv_def, LIST_TYPE_def, list_type_num_def] >> gs[] >>
  simp[WORD_def]
QED

Theorem convDatumList_correct:
  env_asm e conf vs ⇒
  ∃v.
    evaluate s e [convDatumList conf msgs] = (s, Rval [v]) ∧
    LIST_TYPE DATUM msgs v
Proof
  strip_tac >>
  drule_then (strip_assume_tac o SRULE [SKOLEM_THM]) convDatum_correct >>
  gs[env_asm_def, has_v_def] >>
  Induct_on ‘msgs’ >>
  simp[evaluate_def, convDatumList_def, do_con_check_def,
       build_conv_def, LIST_TYPE_def, list_type_num_def] >> gs[]
QED

Theorem normqs_update_cons:
  normalise_queues (fm |+ (k, h::t)) =
  normalise_queues fm |+ (k, h::t)
Proof
  simp[fmap_EXT, normalise_queues_def, FLOOKUP_UPDATE, AllCaseEqs(),
       DRESTRICT_DEF, DISJ_IMP_THM, FORALL_AND_THM, FAPPLY_FUPDATE_THM] >>
  rw[]
  >- (simp[EXTENSION] >> metis_tac[]) >>
  rename [‘FLOOKUP fm k1 = SOME [] ⇒ k2 = k1’] >>
  Cases_on ‘FLOOKUP fm k1 = SOME []’ >> gs[] >> metis_tac[]
QED

Theorem cpFFI_valid_LTau_queue_eq:
  ∀s1 s2 ffi1 ffi2 conf.
    s1.queues = s2.queues ∧ ffi_eq conf ffi1 ffi2
    ⇒ cpFFI_valid conf s1 s2 ffi1 ffi2 LTau
Proof
  rw[cpFFI_valid_def] >>
  simp[some_def] >>
  rw[ELIM_UNCURRY] >>
  spose_not_then kall_tac >>
  pop_assum mp_tac >>
  rw[fmap_eq_flookup,FLOOKUP_normalise_queues,FLOOKUP_UPDATE] >>
  rename1 ‘if a1 = _ then _ else _’ >>
  qexists_tac ‘a1’ >>
  rw[] >>
  simp[qlk_def,fget_def] >>
  TOP_CASE_TAC >> simp[]
QED

Theorem DATUM_exists:
  ∀d. ∃!v. DATUM d v
Proof
  simp[EXISTS_UNIQUE_DEF, FORALL_AND_THM] >> conj_tac >> Induct >>
  simp[LIST_TYPE_def, PULL_EXISTS, WORD_def]
QED

Definition mkDATUM_def:
  mkDATUM d = @v. DATUM d v
End

Theorem DATUM_mkDATUM[simp]:
  DATUM d v ⇔ v = mkDATUM d
Proof
  simp[mkDATUM_def] >> SELECT_ELIM_TAC >> metis_tac[DATUM_exists]
QED

Theorem LTD_exists:
  ∀l. ∃!v. LIST_TYPE DATUM l v
Proof
  simp[EXISTS_UNIQUE_DEF, FORALL_AND_THM] >> conj_tac >>
  Induct >> simp[LIST_TYPE_def, PULL_EXISTS]
QED

Definition mkLTD_def:
  mkLTD l = @v. LIST_TYPE DATUM l v
End

Theorem LTD_mkLTD[simp]:
  LIST_TYPE DATUM l v ⇔ v = mkLTD l
Proof
  simp[mkLTD_def] >> SELECT_ELIM_TAC >> metis_tac[LTD_exists]
QED

Theorem env_asm_REVERSE =
        env_asm_reversef_sem0
          |> SRULE [reffree_Arrow_def, reffree_AppReturns_def, eval_rel0_thm,
                    GSYM LEFT_EXISTS_AND_THM]
          |> Q.GEN ‘vs’

Theorem LTD_CONS:
  Conv (SOME (TypeStamp "::" list_type_num)) [mkDATUM h; mkLTD t] =
  mkLTD (h::t)
Proof
  simp[Excl "LTD_mkLTD", SYM LTD_mkLTD, LIST_TYPE_def, list_type_num_def] >>
  simp[]
QED

Theorem funs_cpEval_valid_nsBind_ps2cs:
  ∀conf cEnv cvs funs x y.
    funs_cpEval_valid conf cEnv cvs funs ⇒
    funs_cpEval_valid conf (cEnv with v := nsBind (ps2cs x) y cEnv.v) cvs funs
Proof
  rw[funs_cpEval_valid_def]>>first_x_assum drule>>
  Cases_on ‘cl’>>Cases_on ‘p’>>rw [closure_cpEval_valid_def]>>
  first_x_assum (irule_at Any)>>first_x_assum (irule_at Any)>>
  simp [nsLookup_nsBind_compute,ps2cs_def,ps2cs2_def]
QED

Definition ep_outgoing_size_def[simp]:
  (ep_outgoing_size binds (Send _ v n e) =
     case FLOOKUP binds v of
       NONE => 0
     | SOME d => 1 + (LENGTH d - n) + ep_outgoing_size binds e) ∧
  ep_outgoing_size _ _ = 0
End

Definition outgoing_size_def[simp]:
  outgoing_size (NPar n1 n2) = outgoing_size n1 + outgoing_size n2 ∧
  outgoing_size NNil = 0 ∧
  outgoing_size (NEndpoint _ s ep) = ep_outgoing_size s.bindings ep
End

Theorem trans_send_decreases_outgoing_size:
  trans c n0 (LSend src msg dest) n ∧ 0 < c.payload_size ⇒
  outgoing_size n < outgoing_size n0
Proof
  Induct_on ‘trans’ >> simp[]
QED

Definition simple_exp_size_def[simp]:
  simple_exp_size (Letrec _ e) = 1n + simple_exp_size e ∧
  simple_exp_size (Let _ e1 e2) = 1 + simple_exp_size e1 + simple_exp_size e2 ∧
  simple_exp_size (If g t e) = 1 + simple_exp_size g + simple_exp_size t +
                               simple_exp_size e ∧
  simple_exp_size (App _ [e1;e2]) =
  1 + simple_exp_size e1 + simple_exp_size e2 ∧
  simple_exp_size (Var _) = 1 ∧
  simple_exp_size (Lit _) = 1
End

Theorem compile_ep_exp_size:
  ∀v1 v2. LENGTH (letfuns ep) ≤ LENGTH v1 ∧
          LENGTH (letfuns ep) ≤ LENGTH v2 ⇒
          simple_exp_size (compile_endpoint c v1 ep) =
          simple_exp_size (compile_endpoint c v2 ep)
Proof
  Induct_on ‘ep’ >>
  simp[compile_endpoint_def, letfuns_def, LENGTH_DROP] >> rw[]
  >- (irule (DECIDE “a = x ∧ b = y ⇒ x + y = a + b : num”) >>
      simp[]) >>
  map_every (fn q => Cases_on q >> gs[]) [‘v1’, ‘v2’] >>
  simp[compile_endpoint_def]
QED

Definition simple_bind_size_def[simp]:
  simple_bind_size (Bind ks ms) = LENGTH ks
End

Theorem simple_bind_size_nsBind[simp]:
  simple_bind_size (nsBind k vv v) = 1 + simple_bind_size v
Proof
  Cases_on ‘v’ >> simp[nsBind_def]
QED

Theorem simple_bind_size_bre[simp]:
  ∀e v. simple_bind_size (build_rec_env fs e v) = simple_bind_size v + LENGTH fs
Proof
  simp[build_rec_env_def] >>
  rpt gen_tac >> SPEC_TAC (“Recclosure e fs”, “G : string -> v”) >>
  gen_tac >> Induct_on ‘fs’ >> simp[FORALL_PROD]
QED

Theorem simple_bind_size_append[simp]:
  simple_bind_size (nsAppend b1 b2) = simple_bind_size b1 + simple_bind_size b2
Proof
  Cases_on ‘b1’ >> Cases_on‘b2’ >> simp[nsAppend_def]
QED

Theorem nsAppend_nsBind_eq:
  v ≠ nsAppend b0 (nsBind k vv (build_rec_env fs e v))
Proof
  disch_then (mp_tac o Q.AP_TERM ‘simple_bind_size’) >>
  simp[]
QED

Definition triR_def:
  triR n (env0,(refs0,ffi0),ev0,k0) (env,(refs,ffi),ev,k) ⇔
    (ffi.io_events = ffi0.io_events ∧
     NRC stepr n (env0,(refs0,ffi0),ev0,k0) (env,(refs,ffi),ev,k) ∨
     ffi.io_events ≠ ffi0.io_events ∧
     ∃env' refs' ffi' ev' k' p.
       NRC stepr n (env0,(refs0,ffi0),ev0,k0) (env',(refs',ffi'),ev',k') ∧
       NRC stepr p (env,(refs,ffi),ev,k) (env',(refs',ffi'),ev',k') ∧
       ffi'.io_events = ffi.io_events)
End

Definition tcdistance_def:
  tcd R a b = (@n. NRC R n a b) - 1
End

Theorem TC_triR0:
  stepr⁺ a b ⇒ ∃n. triR (n + 1) a b
Proof
  map_every PairCases_on [‘a’, ‘b’] >>
  simp[triR_def, TC_eq_NRC, ADD1] >> strip_tac >>
  Cases_on ‘b2.io_events = a2.io_events’ >> simp[] >>
  irule_at Any (NRC |> cj 1 |> iffRL) >> simp[]
QED

Theorem TC_triR[local] =
        TC_triR0 |> Q.GENL[‘a’, ‘b’]
                 |> SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]

val tcd_def = new_specification("tcd_def", ["tcd"], TC_triR)

Theorem triR_one_step_each:
  stepr (ae0,(ar0,af0),av0,ak0) (ae,(ar,af),av,ak) ∧
  stepr (be0,(br0,bf0),bv0,bk0) (be,(br,bf),bv,bk) ∧
  bf.io_events = bf0.io_events ∧ bf0.io_events ≠ af0.io_events ∧
  triR n (ae,(ar,af),av,ak) (be,(br,bf),bv,bk) ⇒
  triR (n + 1) (ae0,(ar0,af0),av0,ak0) (be0,(br0,bf0),bv0,bk0)
Proof
  simp[triR_def] >> strip_tac
  >- (ONCE_REWRITE_TAC [ADD_COMM] >> irule_at Any NRC_ADD_I >>
      simp[] >> first_assum $ irule_at Any >> simp[] >>
      irule_at Any (NRC_1 |> iffRL) >> gs[]) >>
  ONCE_REWRITE_TAC [ADD_COMM] >> irule_at Any NRC_ADD_I >>
  simp[] >> first_assum $ irule_at Any >> simp[] >>
  irule_at Any (NRC |> cj 2 |> iffRL) >> simp[]
QED

Theorem step_iomono:
  stepr (e0,(r0,f0),v0,k0) (e,(r,f),v,k) ⇒ io_events_mono f0 f
Proof
  simp[e_step_reln_def]  >> Cases_on ‘v0’
  >- (rename [‘Exp e0’] >> Cases_on ‘e0’ >>
      dsimp[e_step_def, push_def, return_def, AllCaseEqs(), PULL_EXISTS] >>
      rename [‘smallStep$application op’] >>
      Cases_on ‘op’ >>
      simp[application_def, AllCaseEqs(), PULL_EXISTS, return_def] >> rw[] >>
      drule do_app_io_events_mono >> simp[]) >>
  simp[e_step_def, continue_def, AllCaseEqs(), push_def, return_def] >>
  rw[] >> simp[] >>
  rename [‘smallStep$application op’] >>
  Cases_on ‘op’ >>
  gvs[application_def, AllCaseEqs(), PULL_EXISTS, return_def]>>
  drule do_app_io_events_mono >> simp[]
QED

Theorem NRC_step_iomono:
  NRC stepr n (a0,(a1,a2),a3,a4) (b0,(b1,b2),b3,b4) ⇒
  io_events_mono a2 b2
Proof
  map_every qid_spec_tac
            [‘a0’, ‘a1’, ‘a2’, ‘a3’, ‘a4’, ‘b0’, ‘b1’, ‘b2’, ‘b3’,‘b4’]>>
  Induct_on ‘n’ >> simp[NRC, PULL_EXISTS, FORALL_PROD] >> rw[] >>
  first_assum drule >> drule step_iomono >> metis_tac[io_events_mono_trans]
QED

Theorem triR_step1:
  stepr a0 a ∧ triR n a b ⇒ triR (n + 1) a0 b
Proof
  map_every PairCases_on [‘a0’, ‘b’, ‘a’] >>
  simp[triR_def] >> strip_tac
  >- (Cases_on ‘a2.io_events = a02.io_events’ >> simp[]
      >- (ONCE_REWRITE_TAC [ADD_COMM] >>
          irule_at Any NRC_ADD_I >> simp[]) >>
      irule_at Any (NRC |> cj 1 |> iffRL) >> simp[] >>
      ONCE_REWRITE_TAC [ADD_COMM] >> metis_tac[NRC_ADD_I, NRC_1]) >>
  ‘b2.io_events ≠ a02.io_events’ suffices_by
    (simp[] >> strip_tac >> ONCE_REWRITE_TAC [ADD_COMM] >>
     irule_at Any NRC_ADD_I >> simp[] >> first_assum $ irule_at Any >>
     first_assum $ irule_at Any >> metis_tac[]) >>
  strip_tac >> gs[] >>
  ‘io_events_mono a02 a2’ by metis_tac[step_iomono] >>
  ‘io_events_mono a2 ffi'’ by metis_tac[NRC_step_iomono] >>
  gs[io_events_mono_def] >> metis_tac[IS_PREFIX_ANTISYM]
QED

Theorem RTC_steps =
        RTC_eq_NRC |> Q.ISPEC ‘stepr’ |> iffLR
                   |> SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]

val rtd_def = new_specification("rtd_def", ["rtd"], RTC_steps)

Theorem triR_NRC:
  NRC stepr m a b ∧ triR n b c ⇒ triR (m + n) a c
Proof
  map_every qid_spec_tac [‘m’, ‘a’, ‘b’, ‘c’, ‘n’] >>
  Induct_on ‘m’ >> simp[NRC, PULL_EXISTS] >> rw[] >>
  first_x_assum $ drule_all_then assume_tac >>
  drule_all triR_step1 >> simp[ADD1]
QED

Theorem triR_steps1:
  stepr꙳ a0 a ∧ triR n a b ⇒ triR (n + rtd a0 a) a0 b
Proof
  strip_tac >> drule rtd_def >> metis_tac[triR_NRC, ADD_COMM]
QED

Theorem triR_REFL[simp]:
  ∀x. triR 0 x x
Proof
  simp[triR_def, FORALL_PROD]
QED

Theorem triR_step1R:
  stepr (b00,(b01,b02),b03,b04) (b0,(b1,b2),b3,b4) ∧ 0 < n ∧
  b2.io_events = b02.io_events ∧ a2.io_events ≠ b02.io_events ∧
  triR n (a0,(a1,a2),a3,a4) (b0,(b1,b2),b3,b4) ⇒
  triR n (a0,(a1,a2),a3,a4) (b00,(b01,b02),b03,b04)
Proof
  simp[triR_def] >> rpt strip_tac >> gs[] >> first_assum $ irule_at (Pos hd) >>
  metis_tac[NRC]
QED

Theorem triR_stepsR:
  stepr꙳ (b00,(b01,b02),b03,b04) (b0,(b1,b2),b3,b4) ∧ 0 < n ∧
  b2.io_events = b02.io_events ∧ a2.io_events ≠ b02.io_events ∧
  triR n (a0,(a1,a2),a3,a4) (b0,(b1,b2),b3,b4) ⇒
  triR n (a0,(a1,a2),a3,a4) (b00,(b01,b02),b03,b04)
Proof
  map_every qid_spec_tac
            [‘b00’, ‘b01’, ‘b02’, ‘b03’, ‘b04’, ‘b0’, ‘b1’, ‘b2’, ‘b3’, ‘b4’,
             ‘a0’, ‘a1’, ‘a2’, ‘a3’, ‘a4’] >>
  Induct_on ‘RTC’ >> simp[FORALL_PROD] >> rw[] >> gs[] >>
  qmatch_asmsub_abbrev_tac ‘stepr Ax Bx’ >>
  qmatch_asmsub_abbrev_tac ‘stepr꙳ Bx Cx’ >>
  rename [‘Abbrev(Ax = (_, (_, Af), _, _))’, ‘stepr Ax Bx’, ‘stepr꙳ Bx Cx’,
          ‘Abbrev(Bx = (_, (_, Bf), _, _))’,
          ‘Abbrev(Cx = (_, (_, Cf), _, _))’
          ] >>
  ‘Af.io_events = Bf.io_events’
    by (gs[Abbr‘Ax’, Abbr‘Bx’, Abbr‘Cx’, RTC_eq_NRC] >>
        drule_then assume_tac step_iomono >>
        drule_then assume_tac NRC_step_iomono >>
        gs[io_events_mono_def] >> metis_tac[IS_PREFIX_ANTISYM]) >>
  gs[] >> first_x_assum $ drule_all_then assume_tac >>
  simp[Abbr‘Ax’] >> irule triR_step1R >> metis_tac[]
QED

Theorem simulation:
  ∀p0 pSt0 EP0 L p pSt EP pN0 cEnv0 vs cSt0.
    trans conf (NEndpoint p0 pSt0 EP0) L (NEndpoint p pSt EP) ∧
    cpEval_valid conf p0 cEnv0 pSt0 EP0 pN0 vs cvs cSt0 ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p0 pSt0 EP0) ⇒
          ffi_has_node nd cSt0.ffi.ffi_state) ∧
    (* EP0 does not contain Fix nor Call *)
    letrec_endpoint EP0 ∧
    EVERY (letrec_closure o SND) pSt0.funs ∧
    pletrec_vars_ok EP0 ∧
    EVERY cletrec_vars_ok (MAP SND pSt0.funs) ∧
    can_match conf pN0 L
    ⇒
    ∃cEnv cSt pN vs0 sc.
      triR sc
        (cEnv0, smSt cSt0, Exp (compile_endpoint conf vs EP0), [])
        (cEnv, smSt cSt, Exp (compile_endpoint conf vs0 EP), []) ∧
      (sc = 0 ⇒ outgoing_size pN < outgoing_size pN0) ∧
      cpEval_valid conf p cEnv pSt EP pN vs0 cvs cSt ∧
      cpFFI_valid conf pSt0 pSt cSt0.ffi.ffi_state cSt.ffi.ffi_state L ∧
      (∀nd. nd ∈ network_nodenames (NEndpoint p pSt EP) ⇒
            ffi_has_node nd cSt.ffi.ffi_state)
Proof
  Induct_on ‘trans’ >> simp[compile_endpoint_def] >> rpt strip_tac (* 11 *)
  >- (gs[cpEval_valid_Send] >>
      CONV_TAC (pull_namedexvar_conv "vs0")>>qexists_tac‘vs’>>
      irule_at Any tcd_def >>
      irule_at (Pos hd) break_smallstep_LetNONE >>
      strip_assume_tac
               (small_eval_def |> cj 1 |> iffLR |> GEN_ALL
                |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
                |> INST_TYPE [“:'ffi” |-> “:plffi”]) >>
      pop_assum (irule_at (Pos hd)) >>
      irule_at (Pos hd) (small_big_exp_equiv |> iffRL |> cj 1) >>
      irule_at (Pos hd) (iffRL bigClockTheory.big_clocked_unclocked_equiv) >>
      simp[funBigStepEquivTheory.functional_evaluate] >>
      simp[find_evalform‘Letrec _ _’, Excl "evaluate_var",
           Excl "evaluate_opapp"] >>
      ‘env_asm cEnv0 conf cvs’ by gs[cpEval_valid_def] >>
      simp[find_evalform ‘App _ _’, do_app_thm] >>
      drule_all_then strip_assume_tac cpEval_nsLookup_PLbindings >> simp[] >>
      strip_assume_tac (env_asm_DROP |> Q.INST [‘vs’ |-> ‘cvs’]) >>
      gs[FORALL_AND_THM] >>
      ‘in_module conf.drop’ by gs[env_asm_def] >>
      simp[in_module_nsLookup_build_rec_env] >>
      simp[bind_eq_Rval, PULL_EXISTS, AllCaseEqs(), dec_clock_def] >>
      irule_at (Pos hd) (DECIDE “∀clk. clk + 1n ≠ 0”) >> simp[] >>
      irule_at (Pos hd) (DECIDE “∀clk. x ≤ x + clk + 1n”) >> simp[] >>
      irule_at Any (DECIDE “∀clk. ¬((clk + y + 1) + (x + 2) ≤ x + (y + 2n))”) >>
      simp[] >>
      assume_tac (SRULE [] sendloop_correct) >>
      simp[nsLookup_build_rec_env_sendloop] >>
      gs[cpEval_valid_def] >> pop_assum $ drule_then assume_tac >>
      rename [‘Recclosure _ (sendloop conf dest_s)’] >>
      pop_assum (assume_tac o CONV_RULE (pull_namedallvar_conv "dest")) >>
      pop_assum $ qspec_then ‘MAP (n2w o ORD) dest_s’ mp_tac>>
      simp[MAP_MAP_o, CHR_w2n_n2w_ORD] >>
      qabbrev_tac ‘slv = λe. Recclosure e (sendloop conf dest_s) "sendloop"’ >>
      disch_then (assume_tac o SRULE[markerTheory.Abbrev_def]) >> simp[] >>
      pop_assum (resolve_then (Pos last) assume_tac send_invariant_arg3eq) >>
      pop_assum $ drule_then assume_tac >>
      pop_assum $ mp_tac o SRULE [RIGHT_FORALL_IMP_THM] >>
      impl_tac
      >- (‘∃p x y. cSt0.ffi.ffi_state = (p,x,y)’ by metis_tac[pair_CASES] >>
          gs[valid_send_dest_def,ffi_state_cor_def, MAP_MAP_o,
             CHR_w2n_n2w_ORD]) >>
      disch_then $ strip_assume_tac o SRULE[FORALL_state] >>
      pop_assum $ strip_assume_tac o SRULE[SKOLEM_THM] >>
      pop_assum $ drule_then (strip_assume_tac o SRULE[SKOLEM_THM]) >>
      simp[] >> gs[FORALL_AND_THM]>>
      first_assum (C (resolve_then (Pos hd) assume_tac) $ cj 1 evaluate_clock)>>
      gs[] >>
      first_x_assum (C (resolve_then (Pos hd) (assume_tac o iffLR o cj 2))
                     (evaluate_induce_timeout |> cj 1)) >> gs[] >>
      first_x_assum (resolve_then (Pos hd) assume_tac $
                     DECIDE “∀x y. y ≤ x ⇒ x ≤ (x - y) + y:num”) >>
      gs[DECIDE “y ≤ x ⇒ x - y + y - x = 0n”] >>
      pop_assum $ irule_at (Pos hd) >> simp[] >>
      simp[RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM] >>
      reverse (rpt conj_tac)
      >- (gvs[DISJ_IMP_THM,FORALL_AND_THM] >> rw[] >>
          irule (iffRL update_state_ffi_has_node) >> simp[] >>
          Cases_on ‘cSt0.ffi.ffi_state’ >>
          rename [‘cSt0.ffi.ffi_state = (pn,X)’] >> Cases_on ‘X’ >>
          gs[ffi_state_cor_def])
      >- (simp[cpFFI_valid_def] >>
          Cases_on ‘cSt0.ffi.ffi_state’ >>
          rename [‘cSt0.ffi.ffi_state = (pn,X)’] >> Cases_on ‘X’ >>
          ‘final (pad conf (DROP n d))’
            by rw[final_def, pad_def] >>
          simp[update_state_def, send_events_def, Once compile_message_def,
               comms_ffi_oracle_def, ffi_send_def, pad_LENGTH,
               CHR_w2n_n2w_ORD, MAP_MAP_o] >>
          SELECT_ELIM_TAC >> conj_tac
          >- (simp[AllCaseEqs()] >> DEEP_INTRO_TAC some_intro >> simp[] >>
              ‘valid_send_dest (MAP (n2w o ORD) dest_s) (pn,q,r)’
                by (simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
                    gs[ffi_state_cor_def]) >>
              drule strans_send_cond >> simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
          simp[AllCaseEqs()] >> qx_gen_tac ‘st'’ >>
          DEEP_INTRO_TAC some_intro >> simp[])
      >- (Cases_on ‘cSt0.ffi.ffi_state’ >>
          rename [‘cSt0.ffi.ffi_state = (pn,X)’] >> Cases_on ‘X’ >>
          gs[ffi_state_cor_def]) >>
      irule update_state_send_ffi_state_cor >> simp[] >>
      Cases_on ‘cSt0.ffi.ffi_state’ >>
      rename [‘cSt0.ffi.ffi_state = (pn,X)’] >> Cases_on ‘X’ >>
      gs[ffi_state_cor_def])
  >- ((* second SEND case *) gs[cpEval_valid_Send] >>
      CONV_TAC (pull_namedexvar_conv "vs0")>>qexists_tac ‘vs’>>
      simp[to_small_st_def] >>
      ntac 3 (irule_at Any triR_one_step_each >> simp[e_step_reln_def] >>
              simp[e_step_def, push_def, return_def, continue_def]) >>
      irule_at (Pos hd) triR_steps1 >>
      irule_at (Pos hd) (SRULE [to_small_st_def] RTC_stepr_evaluateL) >>
      irule_at Any RTC_REFL >>
      qmatch_goalsub_abbrev_tac ‘evaluate _ cEnv [dropv]’ >>
      drule_all_then strip_assume_tac cpEval_nsLookup_PLbindings >> simp[] >>
      strip_assume_tac (env_asm_DROP |> Q.INST [‘vs’ |-> ‘cvs’]) >>
      gs[FORALL_AND_THM] >>
      ‘env_asm cEnv0 conf cvs’ by gs[cpEval_valid_def] >>
      ‘in_module conf.drop’ by gs[env_asm_def] >>
      simp[in_module_nsLookup_build_rec_env] >>
      simp[evaluate_opapp, Abbr‘dropv’, Abbr‘cEnv’] >>
      simp[bind_eq_Rval, PULL_EXISTS, AllCaseEqs(), dec_clock_def] >>
      simp[DECIDE “¬(n:num ≤ m) ⇔ m < n”] >> csimp[] >>
      CONV_TAC (pull_namedexvar_conv "vfn") >>
      qexists_tac ‘λs. drop2_v d dd s.refs n s.refs’ >> simp[] >>
      CONV_TAC (pull_namedexvar_conv "ckf1") >>
      qexists_tac
      ‘λs. drop1clk d dd s.refs + drop2clk d dd s.refs n s.refs + 2’ >>
      simp[] >>
      CONV_TAC (pull_namedexvar_conv "rfn") >> qexists_tac ‘λs. []’ >> simp[]>>
      CONV_TAC (pull_namedexvar_conv "ckf2") >> qexists_tac ‘K 0’>> simp[]>>
      simp[continue_def, push_def] >>
      hide_assum "DROP" (qspecl_then [‘ARB’, ‘ARB’] kall_tac) >>

      (* now work a bit on right argument *)
      CONV_TAC (pull_namedexvar_conv "be1") >> qexists_tac ‘cEnv0’ >>
      ntac 8 (irule_at Any triR_step1R >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def,
                   nsLookup_build_rec_env_sendloop]) >>
      use_hidden_assum "DROP" (assume_tac o cj 1) >> simp[] >>
      pop_assum kall_tac >> simp[to_small_st_def] >>
      irule_at Any triR_stepsR >> irule_at (Pos hd) RTC_stepr_evaluateL' >>
      irule_at Any RTC_REFL >>
      simp[eval_rel_def] >>
      use_hidden_assum "DROP" (assume_tac o cj 2) >> simp[] >>
      CONV_TAC (pull_namedexvar_conv "vfn") >>
      qexists_tac ‘drop1_v d (mkDATUM d)’ >> simp[] >>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def] >> pop_assum kall_tac >>
      use_hidden_assum "DROP" (assume_tac o cj 3) >> gs[FAstrefsffi] >>
      pop_assum kall_tac >>
      irule_at Any triR_stepsR >> irule_at (Pos hd) RTC_stepr_evaluateL' >>
      irule_at Any RTC_REFL >>
      simp[eval_rel_def] >>
      use_hidden_assum "DROP" (assume_tac o cj 4) >> gs[FAstrefsffi] >>
      CONV_TAC (pull_namedexvar_conv "vfn") >>
      qexists_tac
        ‘drop2_v d (mkDATUM d) (cSt0.refs ++ droprff cSt0)
         (n + conf.payload_size)’ >>
      simp[] >>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def] >> pop_assum kall_tac >>
      gs[DROP_DROP_T] >>
      ntac 2 (irule_at Any triR_step1R >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def,
                   nsLookup_build_rec_env_sendloop]) >>
      simp[do_opapp_def] >>
      use_hidden_assum "DROP" (assume_tac o cj 5) >> gs[FAstrefsffi] >>

      (* back to left side;
         have to show (.., 𝕍 "sendloop", kont = args=DROP n d) -->₃
                      (.., Exp (drop (n+psz) d), kont = call sendloop)
       *)
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, nsLookup_build_rec_env_sendloop,
           return_def] >>
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, do_opapp_def,
           return_def, continue_def, application_def] >>
      (* have (env with v := DROP n d, Exp (sendloop_code ..), ...) -->₃
              (..., Exp (drop (n+psz) d), kont = ...)    (as before) *)
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, do_opapp_def, push_def,
           return_def, continue_def, application_def] >>
      (* now show padv "x" using padv_correct' *)
      irule_at Any triR_steps1 >> simp[to_small_st_def] >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      qspecl_then [‘cvs’, ‘DROP n d’, ‘conf’]
                  (strip_assume_tac o
                   SRULE[IMP_CONJ_THM, FORALL_AND_THM] o
                   SRULE[SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM])
                  (SRULE [] $ GEN_ALL padv_correct') >>
      simp[bind_eq_Rval, PULL_EXISTS] >>
      last_x_assum (C (resolve_then (Pos hd) mp_tac) $
                    INST_TYPE [beta |-> “:plffi”] evaluate_ffi_intro') >>
      simp[] >>
      disch_then (C (resolve_then (Pos hd) mp_tac) evaluate_add_to_clock) >>
      simp[] >> disch_then $ irule_at Any >> simp[AllCaseEqs()] >>
      CONV_TAC (pull_namedexvar_conv "extra") >> Q.REFINE_EXISTS_TAC ‘ex + 1’ >>
      simp[dec_clock_def] >>
      first_x_assum (C (resolve_then (Pos hd) mp_tac) evaluate_add_to_clock) >>
      simp[] >> strip_tac >>
      CONV_TAC (pull_namedexvar_conv "t") >> qexists_tac ‘cSt0’ >> simp[] >>
      irule_at Any EQ_REFL >> simp[continue_def] >>
      (* ready to proceed with next step of bod0 *)
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, push_def] >>
      pop_assum kall_tac >>
      qpat_x_assum ‘∀x y. env_asm _ _ _ ⇒ do_opapp _ = _’ kall_tac >>
      (* evaluating send (Lit p2, 𝕍 y) *)
      ‘∀v. ∃ns. cSt0.ffi.oracle "send" cSt0.ffi.ffi_state
                    (MAP (λc. n2w (ORD c)) (EXPLODE p2)) (pad conf v) =
                Oracle_return ns (pad conf v) ∧
                strans conf cSt0.ffi.ffi_state (ASend p2 (pad conf v)) ns’
        by (gs[cpEval_valid_def, ffi_state_cor_def, comms_ffi_oracle_def,
               ffi_send_def, pad_LENGTH, AllCaseEqs()] >> gen_tac >>
            DEEP_INTRO_TAC optionTheory.some_intro >>
            simp[MAP_MAP_o, ORD_BOUND, CHR_ORD, IMPLODE_EXPLODE_I] >>
            ‘valid_send_dest (MAP (n2w o ORD) p2) cSt0.ffi.ffi_state’
              suffices_by (strip_tac >> drule strans_send_cond >>
                           simp[MAP_MAP_o, CHR_w2n_n2w_ORD]) >>
            simp[valid_send_dest_def, MAP_MAP_o, CHR_w2n_n2w_ORD] >>
            Cases_on ‘cSt0.ffi.ffi_state’ >>
            rename [‘cSt0.ffi.ffi_state = (pn,X)’] >> Cases_on ‘X’ >>
            gs[ffi_state_cor_def]) >>
      gs[SKOLEM_THM] >>
      ntac 5 (irule_at Any triR_step1 >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def, do_app_thm,
                   to_small_st_def]) >>
      simp[call_FFI_def] >>
      (* evaluating if conf.length x ≤ payload_size conf then .. else .. *)
      ntac 8 (irule_at Any triR_step1 >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def, do_app_thm,
                   to_small_st_def, payload_size_def]) >>
      (* looking at Exp (Var conf.length) *)
      ‘in_module conf.length ∧
       has_v cEnv0.v conf.length (at cvs 2 (DATUM ~~> NUM)) LENGTH’
        by gs[env_asm_def] >>
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def, do_app_thm,
           to_small_st_def, AllCaseEqs(), PULL_EXISTS,
           in_module_nsLookup_build_rec_env, in_module_nsLookup_nsBind] >>
      gvs[has_v_def, at_def] >>
      gs[reffree_Arrow_def, reffree_AppReturns_def, FORALL_AND_THM,
         IMP_CONJ_THM] >>
      first_x_assum (qspec_then ‘DROP n d’ $
                     qx_choosel_then [‘lencl’, ‘lenexp’] strip_assume_tac) >>
      gs[NUM_def, INT_def] >>
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def, do_app_thm,
           to_small_st_def, AllCaseEqs(), PULL_EXISTS] >>
      irule_at (Pos hd) triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_evaluateL' >> irule_at Any RTC_REFL >>
      dxrule_then assume_tac
                  (INST_TYPE [alpha |-> “:plffi”] eval_rel_intro_ffi) >>
      simp[] >>
      simp[continue_def, application_def, do_app_thm, return_def,
           opb_lookup_def] >>
      (* have evaluated If guard to F *)
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, push_def, return_def, continue_def,
           do_if_def] >>
      ntac 4 (pop_assum kall_tac) >>
      (* now up to Let x = drop x (payload_size) in sendloop x *)
      ntac 9 (irule_at Any triR_step1 >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def]) >>
      use_hidden_assum "DROP" (assume_tac o cj 1) >> simp[] >>
      pop_assum kall_tac >>
      irule_at Any triR_steps1 >> irule_at (Pos hd) RTC_stepr_evaluateL' >>
      irule_at Any RTC_REFL >>
      simp[eval_rel_def] >>
      use_hidden_assum "DROP" (assume_tac o cj 2) >> simp[] >>
      CONV_TAC (pull_namedexvar_conv "vfn") >>
      qexists_tac ‘drop1_v (DROP n d) (mkDATUM (DROP n d))’ >> simp[] >>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def] >> pop_assum kall_tac >>
      use_hidden_assum "DROP" (assume_tac o cj 3) >> gs[FAstrefsffi] >>
      pop_assum kall_tac >>
      use_hidden_assum "DROP" (assume_tac o cj 4) >>
      irule_at Any triR_steps1 >> irule_at (Pos hd) RTC_stepr_evaluateL' >>
      irule_at Any RTC_REFL >>
      simp[eval_rel_def] >> gs[FAstrefsffi] >>
      CONV_TAC (pull_namedexvar_conv "vfn") >>
      qexists_tac ‘K $ mkDATUM (DROP conf.payload_size (DROP n d))’ >>
      simp[continue_def] >> pop_assum kall_tac >>
      use_hidden_assum "DROP" (assume_tac o cj 5) >> gs[FAstrefsffi] >>
      pop_assum kall_tac >>
      (* triR over
           left = (Exp (sendloop x), continue = [e],
                   env binds x = drop v n & sendloop & y to padv-loc,
                   ffi has send,
                   st has refs for location of pad data)
           right = Exp (drop v (n + psz)), continue = [sendloop; e],
                   ?env binds just sendloop
       *)
      ntac 5 (irule_at Any triR_step1 >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def,
                   nsLookup_build_rec_env_sendloop]) >>
      simp[do_opapp_def] >>
      (* now have sendloop_code conf p2 on left *)

      (* clean up to show we can now apply triR_REFL *)
      simp[payload_size_def] >>
      gs[cpEval_valid_def, EXstrefsffi] >>
      qmatch_goalsub_abbrev_tac ‘triR _ (_, (new_refs, new_ffi), _, _)’ >>
      map_every (fn (s1,s2) =>
                   CONV_TAC (pull_namedexvar_conv s1) >>
                   qexists_tac [QUOTE s2])
                [("refs", "new_refs"), ("ffi", "new_ffi")] >>
      simp[Abbr‘new_refs’, Abbr‘new_ffi’, DROP_DROP_T] >>
      irule_at (Pos hd) triR_REFL >>

      (* symbolic evaluation all done!!!! *)
      simp[LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] >>
      qmatch_goalsub_abbrev_tac ‘ffi_wf new_ffi’ >>
      ‘ffi_wf new_ffi’ by metis_tac[strans_pres_wf] >>
      ‘(∃nn nq nnet. new_ffi = (nn,nq,nnet)) ∧
       ∃n0 q0 net0. cSt0.ffi.ffi_state = (n0,q0,net0)’
        by metis_tac[pair_CASES] >>
      ‘nn = n0’ by metis_tac[strans_pres_pnum, FST] >>
      gvs[ffi_state_cor_def] >> rpt strip_tac (* 5 *)
      >- (irule match_send_hold_queues_ffi_eq >> metis_tac[])
      >- (simp[cpFFI_valid_def] >> metis_tac[]) >>
      (* 3 *) metis_tac[strans_pres_nodes])
  >- ((* receive, pushing queue *) all_tac >>
      CONV_TAC (pull_namedexvar_conv "vs0")>>qexists_tac‘vs’>>
      qexistsl_tac [‘cEnv0’, ‘cSt0’] >> simp[] >> irule_at Any triR_REFL >>
      drule_then assume_tac can_match_wfLabel >>
      gs[cpEval_valid_def, sem_env_cor_def, pSt_pCd_corr_def] >>
      ‘∃p qs N0. cSt0.ffi.ffi_state = (p,qs,N0)’ by metis_tac[pair_CASES] >>
      gs[ffi_state_cor_def, RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM,
         can_match_def] >>
      rename [‘trans conf pN0 (LSend src msg dest) pN’] >>
      qexists_tac ‘pN’ >> rpt conj_tac >~
      [‘outgoing_size pN < outgoing_size pN0’]
      >- metis_tac[trans_send_decreases_outgoing_size,
                   DECIDE “n ≠ 0n ⇔ 0 < n”] >~
      [‘cpFFI_valid conf s’] >- simp[cpFFI_valid_def] >~
      [‘ffi_eq conf _ (dest,qpush s.queues src msg,pN)’]
      >- (irule_at Any ffi_eq_TRANS >> first_assum $ irule_at Any >>
          gs[can_match_def] >>
          ‘active_trans conf dest (s.queues,pN0) (qpush s.queues src msg,pN)’
            by simp[active_trans_def, emit_trans_def] >>
          dxrule_then assume_tac RTC_SINGLE >>
          drule_all active_trans_equiv_irrel >>
          metis_tac[active_trans_pres_wf]) >~
      [‘ffi_wf (dest,qpush s.queues src msg,pN)’]
      >- metis_tac[trans_pres_ffi_wf] >~
      [‘FLOOKUP (qpush s.queues src msg) _ = SOME _’]
      >- (gs[qpush_def, FLOOKUP_DEF, AllCaseEqs(), qlk_def, fget_def,
             RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] >>
          Cases_on ‘p1 ∈ FDOM s.queues’ >> simp[FAPPLY_FUPDATE_THM] >> rw[] >>
          simp[]) >>
      metis_tac[])
  >- ((* receiveloop - finishing*) all_tac >>
      CONV_TAC (pull_namedexvar_conv "vs0")>>qexists_tac‘vs’>>
      ‘nsLookup cEnv0.c conf.cons = SOME (2, TypeStamp "::" list_type_num) ∧
       nsLookup cEnv0.c conf.nil = SOME (0, TypeStamp "[]" list_type_num)’
        by gvs[env_asm_def, has_v_def, cpEval_valid_def] >>
      simp[to_small_st_def] >>
      ntac 10 (irule_at Any triR_step1 >>
               simp[e_step_def, e_step_reln_def, push_def, return_def,
                    continue_def, application_def, do_app_thm,
                    store_alloc_def, do_opapp_def,
                    nsLookup_build_rec_env_sendloop]) >>
      irule_at Any triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      (* apply convDatumList_correct *)
      qmatch_goalsub_abbrev_tac ‘evaluate _ ENV [convDatumList _ _]’ >>
      ‘env_asm ENV conf cvs’ by gs[Abbr‘ENV’, cpEval_valid_def] >>
      dxrule_then (strip_assume_tac o
                   SRULE [SKOLEM_THM, FORALL_AND_THM])
                  (convDatumList_correct |> INST_TYPE [alpha |-> “:plffi”]) >>
      first_x_assum $ irule_at (Pos hd) >>
      simp[continue_def, push_def, Abbr‘ENV’] >>
      ntac 8 (irule_at Any triR_step1 >>
              simp[e_step_def, e_step_reln_def, continue_def, application_def,
                   return_def, do_opapp_def, push_def,
                   do_app_thm, store_lookup_def, EL_APPEND2, call_FFI_def]) >>
      gs[cpEval_valid_def, comms_ffi_oracle_def, ffi_receive_def,
         MAP_MAP_o, CHR_ORD, IMPLODE_EXPLODE_I] >>
      ‘∃N. (some (m,ns). strans conf cSt0.ffi.ffi_state (ARecv p1 m) ns) =
           SOME (d,N)’
        by (‘∃dn qs0 N0. cSt0.ffi.ffi_state = (dn,qs0,N0)’
              by metis_tac[pair_CASES] >>
            gs[ffi_state_cor_def] >>
            ‘strans conf (dn,s.queues,pN0) (ARecv p1 d)
                    (dn,normalise_queues(s.queues |+ (p1,tl)),pN0)’
              by (irule (hd (CONJUNCTS strans_rules)) >> simp[]) >>
            drule_all_then strip_assume_tac
                           (ONCE_REWRITE_RULE [ffi_eq_SYM] ffi_eq_simulationL)>>
            DEEP_INTRO_TAC some_intro >> simp[FORALL_PROD] >>
            metis_tac[ffi_eq_ARecv]) >>
      simp[] >>
      ‘LENGTH d = conf.payload_size + 1’
        by (gs[pSt_pCd_corr_def, qlk_def, fget_def, AllCaseEqs()] >>
            metis_tac[MEM]) >>
      simp[store_assign_def, store_v_same_type_def, EL_APPEND2, return_def] >>
      ntac 7 (irule_at Any triR_step1 >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def, do_app_thm,
                   store_alloc_def, do_opapp_def, unpadv_def,
                   nsLookup_build_rec_env_sendloop]) >>
      (* Exp (unpadv_code conf) *)
      irule_at Any triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      qmatch_goalsub_abbrev_tac ‘evaluate _ ENV [unpadv_code conf]’ >>
      ‘env_asm ENV conf cvs’ by simp[Abbr‘ENV’] >>
      dxrule_then strip_assume_tac unpadv_correct >>
      ‘LENGTH cSt0.refs < LENGTH (cSt0.refs ++ [W8array d])’ by simp[] >>
      first_x_assum $ dxrule_then strip_assume_tac >>
      gs[Abbr‘ENV’, EL_APPEND2] >> ‘d ≠ []’ by (Cases_on ‘d’ >> gs[]) >>
      first_x_assum $
        dxrule_then (strip_assume_tac o SRULE [SKOLEM_THM, FORALL_AND_THM]) >>
      first_x_assum $ C (resolve_then (Pos hd) assume_tac)
                        (evaluate_ffi_intro' |> INST_TYPE [beta |-> “:plffi”])>>
      gs[] >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      first_x_assum $ irule_at (Pos hd) >> simp[continue_def] >>
      (* Exp (If (finalv "buff") ... ...) *)
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def, do_app_thm, store_lookup_def,
           EL_APPEND1, EL_APPEND2,
           store_alloc_def, do_opapp_def,
           nsLookup_build_rec_env_sendloop] >>
      (* Exp (finalv "buff") *)
      irule_at Any triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      (* apply finalv_correct *)
      irule_at (Pos hd) finalv_correct >>
      simp[store_lookup_def, EL_APPEND1, EL_APPEND2] >>
      simp[continue_def, do_if_def] >> ‘d ≠ []’ by (Cases_on‘d’ >> gs[]) >>
      simp[] >>
      ntac 8 (irule_at Any triR_step1 >>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def, do_app_thm, store_lookup_def,
                   EL_APPEND1, EL_APPEND2, do_con_check_def,
                   store_alloc_def, do_opapp_def, build_conv_def,
                   nsLookup_build_rec_env_sendloop]) >>
      qmatch_goalsub_abbrev_tac ‘triR _ (ENV, _, Exp(Var conf.reverse), _)’>>
      ‘env_asm ENV conf cvs’ by simp[Abbr‘ENV’] >>
      qspec_then ‘cvs’ strip_assume_tac env_asm_REVERSE >>
      last_x_assum drule >> simp[Abbr‘ENV’] >> strip_tac >>
      irule_at Any triR_step1 >> simp[e_step_def, e_step_reln_def, return_def]>>
      pop_assum kall_tac >>
      pop_assum (strip_assume_tac o
                 SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM, IMP_CONJ_THM,
                        FORALL_AND_THM]) >>
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, return_def, continue_def,
           application_def, LTD_CONS]>>
      irule_at (Pos hd) triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      first_x_assum (C (resolve_then (Pos hd) (irule_at Any o iffRL))
                     evaluate_generalise') >>
      simp[continue_def, push_def] >> irule_at Any LESS_EQ_REFL >>
      first_assum $ irule_at (Pat ‘env_asm _ _’) >> pop_assum kall_tac >>
      qspec_then ‘cvs’ strip_assume_tac (Q.GEN ‘vs’ $ SRULE [] env_asm_FLAT) >>
      qmatch_goalsub_abbrev_tac ‘triR _ (ENV, _, _, _)’ >>
      pop_assum $ hide "ENV" >> last_x_assum $ drule_then strip_assume_tac >>
      ntac 2 (irule_at Any triR_step1 >>
              simp[e_step_reln_def, e_step_def, return_def, continue_def,
                   application_def]) >>
      first_x_assum (drule_then strip_assume_tac o SRULE [PULL_EXISTS]) >>
      pop_assum (strip_assume_tac o SRULE [SKOLEM_THM, FORALL_AND_THM]) >>
      simp[] >>
      irule_at (Pos hd) triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      first_x_assum (C (resolve_then (Pos hd) (irule_at Any o iffRL))
                     evaluate_generalise') >> simp[continue_def] >>
      irule_at Any LESS_EQ_REFL >>
      simp[EXstrefsffi] >> irule_at (Pos hd) triR_REFL >> simp[] >>
      (* symbolic evaluation done *)
      simp[LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] >> rpt strip_tac (* 9 *)
      >- gs[funs_cpEval_valid_nsBind_ps2cs]
      >- gs[letfuns_def]
      >- (gs[pSt_pCd_corr_def, FLOOKUP_UPDATE, AllCaseEqs(), EXISTS_OR_THM] >>
          conj_tac >- metis_tac[] >>
          simp[FLOOKUP_normalise_queues, AllCaseEqs()] >>
          dsimp[FLOOKUP_UPDATE, AllCaseEqs()] >>
          gs[qlk_def, fget_def, AllCaseEqs()] >> metis_tac[MEM])
      >- gs[sem_env_cor_def, FLOOKUP_UPDATE, AllCaseEqs(), DISJ_IMP_THM,
            FORALL_AND_THM]
      >- (‘(∃Np Nq Nn. N = (Np,Nq,Nn)) ∧
           (∃Cp Cq Cn. cSt0.ffi.ffi_state = (Cp,Cq,Cn))’
            by metis_tac[pair_CASES] >>
          gvs[ffi_state_cor_def] >> qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
          DEEP_INTRO_TAC some_intro >> simp[] >> strip_tac >>
          drule_then assume_tac strans_pres_pnum >> gvs[] >>
          irule_at (Pos hd) ffi_eq_pres >>
          first_assum $ irule_at Any >> simp[] >>
          irule_at Any (hd $ CONJUNCTS strans_rules) >> simp[] >>
          first_assum $ irule_at Any >> simp[] >> gs[ffi_wf_def])
      >- (‘(∃Np Nq Nn. N = (Np,Nq,Nn)) ∧
           (∃Cp Cq Cn. cSt0.ffi.ffi_state = (Cp,Cq,Cn))’
            by metis_tac[pair_CASES] >>
          qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
          DEEP_INTRO_TAC some_intro >> simp[] >> metis_tac[strans_pres_wf])
      >- (simp[cpFFI_valid_def] >> DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD, normqs_update_cons] >> rw[]
          >- (pop_assum mp_tac >> simp[fmap_EXT, EXTENSION] >> strip_tac >>
              rpt (pop_assum $ qspec_then ‘p1’ mp_tac) >>
              ‘p1 ∈ FDOM s.queues’
                by gvs[qlk_def, fget_def, AllCaseEqs(), FLOOKUP_DEF] >>
              simp[FAPPLY_FUPDATE_THM] >>
              gvs[qlk_def, fget_def, AllCaseEqs(), FLOOKUP_DEF,
                  FAPPLY_normalise_queues] >> rw[]
              >- (qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
                  DEEP_INTRO_TAC some_intro >> simp[])
              >- (qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
                  DEEP_INTRO_TAC some_intro >> simp[]) >>
              gs[FDOM_normalise_queues]) >>
          first_x_assum $ qspecl_then [‘p1’, ‘d’] mp_tac >>
          simp[qlk_def, fget_def] >>
          gvs[normalised_def, qlk_def, fget_def, AllCaseEqs(), FLOOKUP_DEF] >>
          simp[fmap_EXT] >> impl_tac
          >- (simp[EXTENSION] >> metis_tac[])>>
          simp[FAPPLY_FUPDATE_THM, AllCaseEqs()])
      >- (qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
          DEEP_INTRO_TAC some_intro >> simp[] >>
          metis_tac[strans_pres_nodes])
      >- (qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
          DEEP_INTRO_TAC some_intro >> simp[] >>
          metis_tac[strans_pres_nodes]))
  >- ((* receiveloop - continuing *) all_tac >>
      CONV_TAC (pull_namedexvar_conv "vs0")>>qexists_tac‘vs’>>
      ‘nsLookup cEnv0.c conf.cons = SOME (2, TypeStamp "::" list_type_num) ∧
       nsLookup cEnv0.c conf.nil = SOME (0, TypeStamp "[]" list_type_num)’
        by gvs[env_asm_def, has_v_def, cpEval_valid_def] >>
      simp[to_small_st_def] >>
      ntac 10 (irule_at Any triR_step1 >>
               simp[e_step_def, e_step_reln_def, push_def, return_def,
                    continue_def, application_def, do_app_thm,
                    store_alloc_def, do_opapp_def,
                    nsLookup_build_rec_env_sendloop]) >>

      (* do some work on right *)
      (* symbolically evaluate on other side *)
      CONV_TAC (pull_namedexvar_conv "cEnv") >> qexists_tac ‘cEnv0’ >>

      ntac 10 (irule_at Any triR_step1R >>
               simp[e_step_def, e_step_reln_def, push_def, return_def,
                    continue_def, application_def, do_app_thm,
                    store_alloc_def, do_opapp_def,
                    nsLookup_build_rec_env_sendloop]) >>
      (* convDatumList *)
      irule_at Any triR_stepsR >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      irule_at (Pos hd)
               (convDatumList_correct
                  |> INST_TYPE [alpha |-> “:plffi”]
                  |> Q.GEN ‘vs’
                  |> SRULE [LEFT_FORALL_IMP_THM]
                  |> GEN_ALL
                  |> SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM]) >>
      simp[continue_def, push_def] >>
      simp[EXstrefsffi, REVERSE_SNOC] >>
      ntac 2 (irule_at Any triR_step1R >>
              simp[e_step_reln_def, e_step_def, return_def, continue_def,
                   application_def, do_opapp_def]) >>

      (* back to left *)
      irule_at Any triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      (* apply convDatumList_correct *)
      qmatch_goalsub_abbrev_tac ‘evaluate _ ENV [convDatumList _ _]’ >>
      ‘env_asm ENV conf cvs’ by gs[Abbr‘ENV’, cpEval_valid_def] >>
      dxrule_then (strip_assume_tac o
                   SRULE [SKOLEM_THM, FORALL_AND_THM])
                  (convDatumList_correct |> INST_TYPE [alpha |-> “:plffi”]) >>
      first_x_assum $ irule_at (Pos hd) >>
      simp[continue_def, push_def, Abbr‘ENV’] >>
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, continue_def, application_def,
           do_app_thm, store_lookup_def, EL_APPEND2, call_FFI_def] >>
      gs[cpEval_valid_def, comms_ffi_oracle_def, ffi_receive_def,
         MAP_MAP_o, CHR_ORD, IMPLODE_EXPLODE_I] >>
      ‘∃N. (some (m,ns). strans conf cSt0.ffi.ffi_state (ARecv p1 m) ns) =
           SOME (d,N)’
        by (‘∃dn qs0 N0. cSt0.ffi.ffi_state = (dn,qs0,N0)’
              by metis_tac[pair_CASES] >>
            gs[ffi_state_cor_def] >>
            ‘strans conf (dn,s.queues,pN0) (ARecv p1 d)
                    (dn,normalise_queues(s.queues |+ (p1,tl)),pN0)’
              by (irule (hd (CONJUNCTS strans_rules)) >> simp[]) >>
            drule_all_then strip_assume_tac
                           (ONCE_REWRITE_RULE [ffi_eq_SYM] ffi_eq_simulationL)>>
            DEEP_INTRO_TAC some_intro >> simp[FORALL_PROD] >>
            metis_tac[ffi_eq_ARecv]) >>
      simp[] >>
      ‘LENGTH d = conf.payload_size + 1’
        by (gs[pSt_pCd_corr_def, qlk_def, fget_def, AllCaseEqs()] >>
            metis_tac[MEM]) >>
      (* enter receiveloop *)
      irule_at Any triR_step1 >>
      simp[store_assign_def, store_v_same_type_def, EL_APPEND2, return_def,
           e_step_def, e_step_reln_def, continue_def, application_def,
           do_opapp_def] >>
      (* Exp (receiveloop_body conf p1) *)
      ntac 13 (irule_at Any triR_step1 >>
               simp[e_step_def, e_step_reln_def, push_def, return_def,
                    continue_def, application_def, do_app_thm, store_lookup_def,
                    EL_APPEND2, call_FFI_def, comms_ffi_oracle_def, MAP_MAP_o,
                    CHR_w2n_n2w_ORD, CHR_ORD, IMPLODE_EXPLODE_I,
                    store_assign_def, store_v_same_type_def,
                    store_alloc_def, do_opapp_def, unpadv_def, ffi_receive_def,
                    nsLookup_build_rec_env_sendloop]) >>
      irule_at Any triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      qmatch_goalsub_abbrev_tac ‘evaluate _ ENV [unpadv_code conf]’ >>
      ‘env_asm ENV conf cvs’ by simp[Abbr‘ENV’] >>
      dxrule_then strip_assume_tac (SRULE [] unpadv_correct) >>
      ‘LENGTH cSt0.refs < LENGTH (cSt0.refs ++ [W8array d])’ by simp[] >>
      first_x_assum $ dxrule_then strip_assume_tac >>
      gs[Abbr‘ENV’, EL_APPEND2] >> ‘d ≠ []’ by (Cases_on ‘d’ >> gs[]) >>
      first_x_assum $
        dxrule_then (strip_assume_tac o SRULE [SKOLEM_THM, FORALL_AND_THM]) >>
      first_x_assum $ C (resolve_then (Pos hd) assume_tac)
                        (evaluate_ffi_intro' |> INST_TYPE [beta |-> “:plffi”])>>
      gs[] >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      first_x_assum $ irule_at (Pos hd) >> simp[continue_def] >>
      (* If (finalv "buff") ... *)
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def, do_app_thm, store_lookup_def,
           EL_APPEND1, EL_APPEND2,
           store_alloc_def, do_opapp_def,
           nsLookup_build_rec_env_sendloop] >>
      (* Exp (finalv "buff") *)
      irule_at Any triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      CONV_TAC (pull_namedexvar_conv "newrefs") >> qexists_tac ‘[]’ >> simp[] >>
      (* apply finalv_correct *)
      irule_at (Pos hd) finalv_correct >>
      simp[store_lookup_def, EL_APPEND1, EL_APPEND2] >>
      ‘¬final d’ by metis_tac[final_inter_mutexc] >>
      simp[continue_def, do_if_def] >> ‘d ≠ []’ by (Cases_on‘d’ >> gs[]) >>
      simp[] >>
      (* Exp (Letrec [("zerobuf", ...)] ... *)
      qmatch_goalsub_abbrev_tac ‘triR _ (ENV, _, _, _)’ >>
      pop_assum $ hide "ENV" >>
      ‘nsLookup ENV.v (Short "buff") = SOME (Loc (LENGTH cSt0.refs))’
        by (unhide "ENV" >> simp[Abbr‘ENV’]) >>
      ntac 13 (irule_at Any triR_step1 >>
               simp[e_step_def, e_step_reln_def, do_con_check_def, push_def,
                    build_rec_env_def, do_app_thm, store_lookup_def, EL_APPEND2,
                    return_def, continue_def, application_def, do_opapp_def,
                    opn_lookup_def, integerTheory.INT_SUB]) >>
      (* Exp zerobuf_code *)
      irule_at Any triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_changerefs_evaluateL >>
      ‘LENGTH cSt0.refs < LENGTH (cSt0.refs ++ [W8array d])’ by simp[] >>
      dxrule zerobuf_correct >> simp[EL_APPEND2] >>
      ‘conf.payload_size < conf.payload_size + 1’ by simp[] >>
      disch_then dxrule >>
      qmatch_goalsub_abbrev_tac ‘evaluate _ ENV1 [zerobuf_code]’ >>
      CONV_TAC (LAND_CONV (pull_namedallvar_conv "e")) >>
      disch_then $ qspec_then ‘ENV1’ mp_tac >>
      simp[Abbr‘ENV1’, DROP_LENGTH_TOO_LONG] >>
      disch_then (strip_assume_tac o SRULE [SKOLEM_THM]) >>
      pop_assum $ irule_at Any >> unhide "ENV" >>
      simp[continue_def, Abbr‘ENV’] >> pop_assum kall_tac >>
      ntac 9 (irule_at (Pos hd) triR_step1 >>
              simp[e_step_reln_def, e_step_def, push_def, return_def,
                   do_con_check_def, continue_def, build_conv_def, LTD_CONS,
                   application_def, do_opapp_def]) >>
      simp[unpadv_def, build_rec_env_def, EXstrefsffi] >>

      irule_at (Pos hd) triR_REFL >>
      (* symbolic evaluation done! *)
      simp[LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM,
           ffi_state_component_equality] >>
      gs[letfuns_def] >>
      qpat_x_assum ‘$some _ = _’ mp_tac >> DEEP_INTRO_TAC some_intro >>
      simp[FORALL_PROD] >>
      ‘∃nnm qs0 N0. cSt0.ffi.ffi_state = (nnm,qs0,N0)’
        by metis_tac[pair_CASES] >> rpt gen_tac >> strip_tac >> strip_tac >>
      gvs[] >>
      rename [‘strans _ _ _ (nnm', qs, N)’] >> rpt strip_tac (* 8 *)
      >- (gs[pSt_pCd_corr_def, FLOOKUP_normalise_queues, AllCaseEqs()] >>
          gs[qlk_def, fget_def, FLOOKUP_DEF, DISJ_IMP_THM, FORALL_AND_THM,
             RIGHT_AND_OVER_OR, AllCaseEqs()] >>
          simp[FAPPLY_FUPDATE_THM, AllCaseEqs()] >> rw[] >>
          metis_tac[MEM])
      >- gs[sem_env_cor_def]
      >- (gs[ffi_state_cor_def] >> drule strans_pres_pnum >> simp[] >>
          strip_tac >> gvs[] >>
          irule_at (Pos hd) ffi_eq_pres >>
          first_assum $ irule_at Any >> simp[] >>
          irule_at Any (hd $ CONJUNCTS strans_rules) >> simp[] >>
          first_assum $ irule_at Any >> simp[] >> gs[ffi_wf_def])
      >- metis_tac[strans_pres_wf]
      >- (gs[cpFFI_valid_def] >> DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD, normqs_update_cons] >> rw[]
          >- (pop_assum mp_tac >> simp[fmap_EXT, EXTENSION] >> strip_tac >>
              rpt (pop_assum $ qspec_then ‘p1’ mp_tac) >>
              ‘p1 ∈ FDOM s.queues’
                by gvs[qlk_def, fget_def, AllCaseEqs(), FLOOKUP_DEF] >>
              simp[FAPPLY_FUPDATE_THM] >>
              gvs[qlk_def, fget_def, AllCaseEqs(), FLOOKUP_DEF,
                  FAPPLY_normalise_queues] >> rw[] >> simp[] >>
              gs[FDOM_normalise_queues]) >>
          first_x_assum $ qspecl_then [‘p1’, ‘d’] mp_tac >>
          simp[qlk_def, fget_def] >>
          gvs[normalised_def, qlk_def, fget_def, AllCaseEqs(), FLOOKUP_DEF] >>
          simp[fmap_EXT] >> impl_tac
          >- (simp[EXTENSION] >> metis_tac[])>>
          simp[FAPPLY_FUPDATE_THM, AllCaseEqs()]) >>
      metis_tac[strans_pres_nodes])
  >- ((* if 1 *) all_tac>>
      ‘nsLookup cEnv0.c conf.cons = SOME (2, TypeStamp "::" list_type_num) ∧
       nsLookup cEnv0.c conf.nil = SOME (0, TypeStamp "[]" list_type_num)’
        by gvs[env_asm_def, has_v_def, cpEval_valid_def]>>
      qmatch_asmsub_abbrev_tac ‘(2,lcons)’>>
      qmatch_asmsub_abbrev_tac ‘(0,lnil)’>>
      ‘nsLookup cEnv0.v (Short (ps2cs v)) =
       SOME (Conv (SOME lcons) [Litv (Word8 1w); Conv (SOME lnil) []])’
      by (gvs[sem_env_cor_def, cpEval_valid_def,Abbr‘lcons’,Abbr‘lnil’,
              Excl "LTD_mkLTD", Excl "DATUM_mkDATUM"]>>
          first_x_assum drule >>
          rw[Excl "DATUM_mkDATUM"] >>
          gs[Excl "DATUM_mkDATUM", LIST_TYPE_def,WORD_def,list_type_num_def])>>
      simp[to_small_st_def,w1ckV_def] >>
      ntac 11 (irule_at Any triR_step1 >>
               simp[e_step_def, e_step_reln_def, push_def, return_def,
                    continue_def, application_def, do_app_thm,build_conv_def,
                    store_alloc_def, do_opapp_def,do_con_check_def,do_if_def])>>
      irule_at Any triR_REFL>>
      qexists_tac ‘pN0’>> simp[] >> rpt conj_tac (* 3 *) >~
      [‘cpEval_valid _ _ _ _ _ _ (TAKE _ _)’]
      >- gs[cpEval_valid_def,letfuns_def,enc_ok_take,pSt_pCd_corr_def] >~
      [‘cpFFI_valid’] >- simp[cpFFI_valid_LTau_queue_eq] >>
      metis_tac[])
  >- ((* if 2 *) all_tac>>
      ‘nsLookup cEnv0.c conf.cons = SOME (2, TypeStamp "::" list_type_num) ∧
       nsLookup cEnv0.c conf.nil = SOME (0, TypeStamp "[]" list_type_num)’
        by gvs[env_asm_def, has_v_def, cpEval_valid_def]>>
      qmatch_asmsub_abbrev_tac ‘(2,lcons)’>>
      qmatch_asmsub_abbrev_tac ‘(0,lnil)’>>
      ‘∃v'. nsLookup cEnv0.v (Short (ps2cs v)) = SOME v' ∧
            do_eq v' (Conv (SOME lcons) [Litv (Word8 1w);
                                         Conv (SOME lnil) []]) = Eq_val F’
      by (gvs[sem_env_cor_def, cpEval_valid_def,Abbr‘lcons’,Abbr‘lnil’,
              Excl "DATUM_mkDATUM", Excl "LTD_mkLTD"]>>
          first_x_assum drule>> rw[Excl "DATUM_mkDATUM"] >>
          first_x_assum (irule_at Any) >>
          Cases_on ‘w’>>
          gs[LIST_TYPE_def,WORD_def,list_type_num_def, Excl "DATUM_mkDATUM",
             do_eq_def,ctor_same_type_def,same_type_def,
             lit_same_type_def]>>
          rw[]>>rveq>>
          Cases_on ‘t’>>
          gs[LIST_TYPE_def,WORD_def,list_type_num_def,Excl "DATUM_mkDATUM",
             do_eq_def,ctor_same_type_def,same_type_def,
             lit_same_type_def])>>
      simp[to_small_st_def,w1ckV_def]>>
      ntac 11 (irule_at Any triR_step1>>
               simp[e_step_def, e_step_reln_def, push_def, return_def,
                    continue_def, application_def,do_app_thm,build_conv_def,
                    store_alloc_def, do_opapp_def,do_con_check_def,do_if_def]) >>
      irule_at Any triR_REFL>>
      qexists_tac ‘pN0’>> rpt conj_tac >> simp[] (* 3 *)
      >- gs[cpEval_valid_def,letfuns_def,enc_ok_drop,pSt_pCd_corr_def]
      >- simp[cpFFI_valid_LTau_queue_eq]
      >- metis_tac[])
  >- ((* let *) all_tac>>
      ‘nsLookup cEnv0.c conf.cons = SOME (2, TypeStamp "::" list_type_num) ∧
       nsLookup cEnv0.c conf.nil = SOME (0, TypeStamp "[]" list_type_num)’
        by gvs[env_asm_def, has_v_def, cpEval_valid_def]>>
      ‘∃x xs f'. vs = x::xs ∧ enc_ok conf cEnv0 (letfuns e) xs ∧
             nsLookup cEnv0.v (getLetID conf x) = SOME f' ∧
             (LIST_TYPE DATUM --> DATUM) f f'’
        by (gs[cpEval_valid_def,letfuns_def]>>Cases_on‘vs’>>
            gs[enc_ok_def]>>first_x_assum (irule_at Any)>>
            simp[])>> rveq >>
      simp[to_small_st_def,compile_endpoint_def]>>
      irule_at Any triR_step1>>
      simp[e_step_def, e_step_reln_def,
           push_def, return_def,continue_def]>>
      irule_at Any triR_steps1>>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      simp[evaluate_def] >>
      ‘∃vs. LIST_TYPE DATUM (MAP (THE o FLOOKUP s.bindings) vl) vs ∧
         ∀(st : plffi state).
           evaluate st cEnv0
                    [convList conf (MAP (Var ∘ Short ∘ ps2cs) vl)] =
           (st,Rval [vs])’
        by (gs[cpEval_valid_def,Excl "LTD_mkLTD"]>>
            ntac 2 (qpat_x_assum ‘nsLookup cEnv0.c _ = _’ mp_tac)>>
            qpat_x_assum ‘sem_env_cor _ _ _ _’ mp_tac>>
            last_x_assum mp_tac>>
            rpt (pop_assum kall_tac)>>
            simp[AND_IMP_INTRO]>>
            Induct_on‘vl’>>rw[convList_def]>>rw[evaluate_def,build_conv_def]>>
            gs[do_con_check_def]
            >- simp[SYM LTD_mkLTD, Excl "LTD_mkLTD", LIST_TYPE_def,
                    list_type_num_def] >>
            simp[bind_eq_Rval, AllCaseEqs(), PULL_EXISTS] >>
            gs[sem_env_cor_def,IS_SOME_EXISTS]>>
            first_x_assum drule>>rw[LTD_CONS])>>
      simp[]>>pop_assum kall_tac>>
      gs[Arrow_def,AppReturns_thm,AllCaseEqs(),PULL_EXISTS]>>
      first_x_assum $
        qspec_then ‘MAP (THE o FLOOKUP s.bindings) vl’ strip_assume_tac >>
      CONV_TAC (pull_namedexvar_conv "clk1") >>
      Q.REFINE_EXISTS_TAC ‘SUC clk1’>>simp[dec_clock_def]>>
      gs[eval_rel_def]>>pop_assum(qspec_then‘cSt0.refs’assume_tac)>>gs[]>>
      (iffRL evaluate_generalise' |> irule_at (Pos hd)) >>
      first_x_assum $ irule_at (Pos hd) >>
      simp[continue_def]>> irule_at (Pos hd) EQ_REFL >>
      CONV_TAC (pull_namedexvar_conv "cSt") >>
      qexists_tac ‘cSt0 with  refs := cSt0.refs ++ refs'’>>
      simp[]>>irule_at Any triR_REFL>>
      qexistsl_tac [‘pN0’,‘ck1’]>>simp[]>>
      rpt(conj_tac)  (* 3 *)
      >- (gs[cpEval_valid_def,pSt_pCd_corr_def,
             sem_env_cor_def,funs_cpEval_valid_nsBind_ps2cs]>>
          rw[FLOOKUP_UPDATE,nsBind_def,nsLookup_def]>>simp[])
      >- simp[cpFFI_valid_LTau_queue_eq]
      >- metis_tac[])
  >- ((* fix *) gs[letrec_endpoint_def])
  >- ((* letrec *) all_tac >>
      qpat_x_assum ‘EVERY (letrec_closure o SND) _’ kall_tac>>
      qpat_x_assum ‘letrec_endpoint _’ kall_tac>>
      CONV_TAC (pull_namedexvar_conv "vs0")>>qexists_tac‘vs’>>
      gs[cpEval_valid_def, pSt_pCd_corr_def, DISJ_IMP_THM, FORALL_AND_THM] >>
      ntac 2 (irule_at (Pos hd) triR_step1 >>
              simp[e_step_def, e_step_reln_def, build_rec_env_def, push_def,
                   return_def, AllCaseEqs()]) >>
      irule_at (Pos hd) triR_steps1 >>
      irule_at (Pos hd) RTC_stepr_evaluateL >> irule_at Any RTC_REFL >>
      simp[find_evalform ‘Con _ _’, bind_eq_Rval, PULL_EXISTS] >>
      qpat_abbrev_tac ‘E = cEnv0 with v := _ ’ >>
      qpat_x_assum ‘∀v. MEM _ vars ⇒ _’
                   (qx_choose_then ‘vval’ assume_tac o
                    SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])>>
      gs[sem_env_cor_def, Excl "DATUM_mkDATUM"] >>
      ‘∀vn. MEM vn vars ⇒ ∃v'. nsLookup cEnv0.v (Short (ps2cs vn)) = SOME v' ∧
                               DATUM (vval vn) v'’ by metis_tac[]>>
      pop_assum (qx_choose_then ‘VVAL’ assume_tac o
                 SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM,
                        Excl "DATUM_mkDATUM"]) >>
      gs[letfuns_def, Excl "DATUM_mkDATUM"] >>
      ‘∀s:plffi state.
         evaluate s E (REVERSE $ MAP (Var o Short o ps2cs) vars) =
         (s, Rval (REVERSE $ MAP VVAL vars))’
        by (‘∀s:plffi state rn rv. evaluate s
                                (cEnv0 with v:= nsBind (ps2cs2 rn) rv cEnv0.v)
                                (REVERSE( MAP (Var o Short o ps2cs) vars)) =
                       (s, Rval (REVERSE $ MAP VVAL vars))’
              suffices_by simp[Abbr‘E’] >>
            RM_ABBREV_TAC "E" >> qpat_x_assum ‘ALL_DISTINCT vars’ kall_tac >>
            Induct_on ‘vars’ using SNOC_INDUCT >> simp[] >> rpt strip_tac >>
            gs[MAP_SNOC, REVERSE_SNOC, EVERY_SNOC] >>
            simp[Once evaluate_cons] >>
            gs[ps2cs_def, ps2cs2_def]) >>
      simp[] >> simp[FORALL_state] >>
      CONV_TAC (pull_namedexvar_conv "rfn") >>
      qexists_tac ‘K []’ >> simp[] >>
      map_every (fn s => CONV_TAC (pull_namedexvar_conv s))
                ["vfn", "ckf1", "ckf2"] >>
      qexistsl_tac [‘K 0’, ‘K 0’, ‘K (Conv NONE (MAP VVAL vars))’] >> simp[] >>
      simp[continue_def, push_def] >>
      irule_at (Pos hd) triR_step1 >> simp[e_step_def, e_step_reln_def] >>
      qmatch_asmsub_abbrev_tac ‘nsBind (ps2cs2 _) clv’ >>
      ‘nsLookup E.v (Short (ps2cs2 dn)) = SOME clv’ by simp[Abbr‘E’]>>
      simp[return_def] >>
      irule_at (Pos hd) triR_step1 >>
      simp[e_step_def, e_step_reln_def, continue_def, application_def] >>
      simp[do_opapp_def, Abbr‘clv’] >>
      irule_at (Pos hd) triR_step1 >>
      simp[e_step_def, e_step_reln_def, continue_def, push_def] >>
      irule_at (Pos hd) triR_step1 >>
      simp[e_step_def, e_step_reln_def, continue_def, push_def, return_def] >>
      irule_at (Pos hd) triR_step1 >>
      simp[e_step_def, e_step_reln_def, continue_def, push_def, return_def,
           can_pmatch_all_def, terminationTheory.pmatch_def,
           AllCaseEqs()] >>
      irule_at Any triR_step1 >>
      simp[e_step_def, e_step_reln_def, continue_def, AllCaseEqs(),
           astTheory.pat_bindings_def, pat_bindings_MAP_Pvar,
           MAP_REVERSE] >>
      csimp[pmatch_tuple_MAP_Pvar, terminationTheory.pmatch_def] >>
      irule_at Any triR_REFL >>
      simp[LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM, nsAppend_nsBind_eq,
           sem_env_component_equality] >> rpt strip_tac
      >- ((* vars in letrec binding all distinct *) all_tac >>
          irule ALL_DISTINCT_MAP_INJ >> simp[ps2cs_def])
      >- (gs[funs_cpEval_valid_def]>>rw[]
          >- ((* The new functions is fine *) all_tac>>
              simp[closure_cpEval_valid_def]>>
              first_x_assum (irule_at Any)>>
              first_x_assum (irule_at Any)>>
              simp[nsLookup_nsAppend_Short, AllCaseEqs(),IS_SOME_EXISTS,
                   namespacePropsTheory.nsLookup_alist_to_ns_none,
                   namespacePropsTheory.nsLookup_alist_to_ns_some,
                   alistTheory.ALOOKUP_FAILS, MEM_MAP, ps2cs_def,
                   build_rec_env_def, ps2cs2_def])
          >- (Cases_on ‘cl’>>PairCases_on ‘p'’>>
              rename1 ‘Closure args0 (funs0,bindings0) e0’>>
              gs [closure_cpEval_valid_def]>>
              first_x_assum (pop_assum o mp_then Any mp_tac)>>
              rw[closure_cpEval_valid_def]>>
              first_x_assum (irule_at Any)>>
              gs[nsLookup_nsAppend_Short, AllCaseEqs(),
                 namespacePropsTheory.nsLookup_alist_to_ns_some,
                 namespacePropsTheory.nsLookup_alist_to_ns_none,
                 alistTheory.ALOOKUP_FAILS, MEM_MAP, ps2cs_def,
                 build_rec_env_def, ps2cs2_def]))
      >- gs[FLOOKUP_DEF, AllCaseEqs()] (* v's all bound *)
      >- (simp[nsLookup_nsAppend_Short, AllCaseEqs(),
               namespacePropsTheory.nsLookup_alist_to_ns_none,
               namespacePropsTheory.nsLookup_alist_to_ns_some,
               alistTheory.ALOOKUP_FAILS, MEM_MAP, ps2cs_def,
               build_rec_env_def, ps2cs2_def
               ] >>
          dsimp[] >> Cases_on ‘MEM n vars’ >> simp[]
          >- (RM_ABBREV_TAC "E" >>
              map_every (C qpat_x_assum kall_tac)
                        [‘ALL_DISTINCT vars’, ‘nsLookup E.v _ = SOME _’,
                         ‘∀s. evaluate _ E (REVERSE _) = _’] >>
              Induct_on‘ vars’ using SNOC_INDUCT >>
              simp[EVERY_SNOC, REVERSE_SNOC, MAP_SNOC] >> rw[] >>
              gs[] >> metis_tac[]) >>
          gs[ps2cs_def] >> metis_tac[])
      >- (simp[cpFFI_valid_def] >>
          simp[some_def] >>
          rw[ELIM_UNCURRY] >>
          spose_not_then kall_tac >>
          pop_assum mp_tac >>
          rw[fmap_eq_flookup,FLOOKUP_normalise_queues,FLOOKUP_UPDATE] >>
          rename1 ‘if a1 = _ then _ else _’ >>
          qexists_tac ‘a1’ >>
          rw[] >>
          simp[qlk_def,fget_def] >>
          TOP_CASE_TAC >> simp[])
      >- (gvs[regexpTheory.LIST_UNION_def,MEM_LIST_UNION,MEM_MAP,PULL_EXISTS]))
  >- ((* FCall *) all_tac>>
      simp[to_small_st_def,compile_endpoint_def]>>
      irule_at Any triR_step1>>
      simp[e_step_def, e_step_reln_def, push_def, return_def,
           continue_def, application_def,do_app_thm,build_conv_def,
           store_alloc_def, do_opapp_def,do_con_check_def,do_if_def]>>
      irule_at Any triR_steps1>>
      irule_at (Pos hd) RTC_stepr_fixedstate_evaluateL >>
      simp[] >>
      ‘∃vs. LIST_REL DATUM (MAP (THE o FLOOKUP s.bindings) args) vs ∧
            (∀(cEnv0': v sem_env) refs.
                 pmatch cEnv0'.c refs
                   (Pcon NONE (MAP (Pvar ∘ ps2cs) params))
                   (Conv NONE vs) [] =
                 Match (REVERSE (ZIP (MAP ps2cs params,vs)))) ∧
         ∀(st : plffi state).
           evaluate st cEnv0
                    [Con NONE (MAP (Var ∘ Short ∘ ps2cs) args)] =
           (st,Rval [Conv NONE vs])’
        by (gs[cpEval_valid_def, Excl "LTD_mkLTD"]>>
            qpat_x_assum ‘sem_env_cor _ _ _ _’ mp_tac>>
            qpat_x_assum ‘LENGTH args = LENGTH params’ mp_tac>>
            qpat_x_assum ‘EVERY _ args’ mp_tac>>
            rpt (pop_assum kall_tac)>>
            simp[AND_IMP_INTRO, Excl "LTD_mkLTD"]>>
            MAP_EVERY (W (curry Q.SPEC_TAC)) [‘params’,‘args’]>>
            Induct_on‘args’ using SNOC_INDUCT>>
            rw[evaluate_def,build_conv_NONE,Excl "LTD_mkLTD"]
            >-simp[can_pmatch_all_def,terminationTheory.pmatch_def]>>
            qspec_then‘params’ mp_tac SNOC_CASES>>
            rw[Excl "LTD_mkLTD"] >> gs[Excl "LTD_mkLTD"] >>
            first_x_assum(qspec_then‘l’assume_tac)>>
            gs[EVERY_SNOC,LIST_REL_SNOC,MAP_SNOC,Excl "LTD_mkLTD",
               Excl "DATUM_mkDATUM"] >>
            simp[PULL_EXISTS,Excl "LTD_mkLTD", Excl "DATUM_mkDATUM"]>>
            first_x_assum (irule_at Any)>>
            gs[sem_env_cor_def,IS_SOME_EXISTS,Excl "DATUM_mkDATUM"]>>
            first_x_assum drule>>rw[Excl "DATUM_mkDATUM"]>>
            simp[Excl "DATUM_mkDATUM"]>>
            first_x_assum (irule_at Any)>>rw[]
            >-(first_x_assum (qspecl_then[‘cEnv0'’,‘refs’] assume_tac)>>
               gs[terminationTheory.pmatch_def]>>
               ‘LENGTH l = LENGTH vs’ by spose_not_then (gs o single)>>
               gs[can_pmatch_all_def,terminationTheory.pmatch_def]>>
               ‘LENGTH (MAP ps2cs (SNOC x' l)) = LENGTH (vs ++ [v'])’
                by gs[LENGTH_MAP]>>
               drule pmatch_list_MAP_Pvar>>simp[MAP_MAP_o,MAP_SNOC,SNOC_APPEND])
            >- (first_x_assum (qspec_then‘st’
                  (assume_tac o SIMP_RULE std_ss [evaluate_def]))>>
                gvs[do_con_check_def,build_conv_def,AllCaseEqs(),REVERSE_SNOC]>>
                simp[evaluate_cons]))>>
      simp[]>>
      CONV_TAC (pull_namedexvar_conv "newrefs") >>
      Q.REFINE_EXISTS_TAC ‘[]’>>simp[GSYM PULL_EXISTS,continue_def,push_def]>>
      ‘closure_cpEval_valid conf cEnv0 cvs dn (Closure params (funs,bindings) e)’
      by gs[cpEval_valid_def,funs_cpEval_valid_def]>>
      gs[closure_cpEval_valid_def]>>
      first_x_assum(qspecl_then[‘cEnv0'’,‘cSt0.refs’]assume_tac)>>
      gs[Excl "DATUM_mkDATUM"]>>
      ‘ALL_DISTINCT (MAP ps2cs params)’
        by (qpat_x_assum ‘ALL_DISTINCT _’ mp_tac>>rpt(pop_assum kall_tac)>>
            Induct_on‘params’>>rw[ps2cs_def,MEM_MAP])>>
      ntac 6 (irule_at Any triR_step1>>
              simp[e_step_def, e_step_reln_def, push_def, return_def,
                   continue_def, application_def,do_app_thm,build_conv_def,
                   ALL_DISTINCT_REVERSE,can_pmatch_all_EVERY,
                   astTheory.pat_bindings_def,MAP_REVERSE,
                   store_alloc_def, do_opapp_def,do_con_check_def,do_if_def])>>
      irule_at Any triR_REFL>>
      qexists_tac‘pN0’>>simp[]>>
      rpt(conj_tac) (* 3 *)
      >- (gs[cpEval_valid_def,Excl "LTD_mkLTD",Excl "DATUM_mkDATUM"]>>
          rpt conj_tac
          >- (‘LENGTH (MAP ps2cs params) = LENGTH vs'’
                by (drule LIST_REL_LENGTH>>simp[LENGTH_MAP])>>
              gs[funs_cpEval_valid_def]>>rw[]
              >- (first_x_assum drule>>rw[closure_cpEval_valid_def]>>
                  first_x_assum (irule_at Any)>>
                  gs[nsLookup_nsAppend_Short, AllCaseEqs(),
                     namespacePropsTheory.nsLookup_alist_to_ns_some,
                     namespacePropsTheory.nsLookup_alist_to_ns_none,
                     alistTheory.ALOOKUP_FAILS, MEM_MAP, ps2cs_def,
                     build_rec_env_def, ps2cs2_def]>>
                  disj1_tac>>CCONTR_TAC>>gs[MEM_ZIP,ps2cs_def,EL_MAP])
              >- (Cases_on ‘cl’>>PairCases_on ‘p'’>>
                  rename1 ‘Closure args0 (funs0,bindings0) e0’>>
                  gs [closure_cpEval_valid_def]>>
                  first_x_assum (pop_assum o mp_then Any mp_tac)>>
                  rw[closure_cpEval_valid_def]>>
                  first_x_assum (irule_at Any)>>
                  gs[nsLookup_nsAppend_Short, AllCaseEqs(),
                     namespacePropsTheory.nsLookup_alist_to_ns_some,
                     namespacePropsTheory.nsLookup_alist_to_ns_none,
                     alistTheory.ALOOKUP_FAILS, MEM_MAP, ps2cs_def,
                     build_rec_env_def, ps2cs2_def]>>
                  disj1_tac>>CCONTR_TAC>>gs[MEM_ZIP,ps2cs_def,EL_MAP]))
          >- (gs[pSt_pCd_corr_def,Excl "LTD_mkLTD"]>>conj_tac
              >- (rw[flookup_update_list_some]>>Cases_on ‘MEM vn params’
                  >- (simp[EXISTS_OR_THM]>>disj1_tac>>
                      ‘ALL_DISTINCT (MAP FST (REVERSE (ZIP (params,MAP (THE ∘ FLOOKUP s.bindings) args))))’
                        by gs[MAP_ZIP,ALL_DISTINCT_REVERSE,LENGTH_REVERSE,MAP_REVERSE]>>
                      drule MEM_ALOOKUP>>disch_then (irule_at Any o iffLR)>>
                      simp[MEM_REVERSE,MEM_ZIP]>>gs[MEM_EL]>>asm_exists_tac>>simp[])
                    >- (simp[EXISTS_OR_THM]>>disj2_tac>>first_x_assum drule>>
                        rw[IS_SOME_EXISTS]>>pop_assum (irule_at Any)>>
                        gs[ALOOKUP_FAILS,MEM_ZIP,MEM_MAP,MEM_EL]))
              >- metis_tac[ALOOKUP_MEM,wfclosure_def])
          >- (rw[namespacePropsTheory.nsLookup_nsAppend_some,sem_env_cor_def,
                 id_to_mods_def,build_rec_env_def,nsLookup_nsBind_compute,
                 Excl "LTD_mkLTD",Excl "DATUM_mkDATUM"]>>
              ‘¬("" = ps2cs n) ∧ ¬(ps2cs2 dn = ps2cs n)’
                by simp[ps2cs_def,ps2cs2_def]>>
              simp[Excl "DATUM_mkDATUM"]>>
              gs[flookup_update_list_some,Excl "LTD_mkLTD",
                 Excl "DATUM_mkDATUM"]
              >- (drule ALOOKUP_MEM>>
                  simp[MEM_REVERSE,MEM_ZIP,LENGTH_MAP,Excl "DATUM_mkDATUM"]>>
                  rw[Excl "DATUM_mkDATUM"]>>
                  drule (iffLR LIST_REL_EL_EQN)>>
                  rw[LENGTH_MAP,Excl "DATUM_mkDATUM"]>>
                  pop_assum(qspec_then‘n'’ mp_tac)>>
                  simp[Excl "DATUM_mkDATUM"]>>disch_then (irule_at Any)>>
                  disj1_tac>>
                  simp[namespacePropsTheory.nsLookup_alist_to_ns_some]>>
                  irule ALOOKUP_ALL_DISTINCT_MEM>>
                  conj_tac
                  >- (simp[MAP_REVERSE]>>
                      ‘LENGTH (MAP ps2cs params) = LENGTH vs'’
                      by (drule LIST_REL_LENGTH>>simp[LENGTH_MAP])>>
                      simp[MAP_ZIP])
                  >- (simp[MEM_REVERSE,LENGTH_MAP,MEM_ZIP]>>qexists_tac‘n'’>>
                      simp[Req0 EL_MAP]))
              >- (first_x_assum
                  (qpat_x_assum ‘FLOOKUP bindings _ = _’ o mp_then Any
                   assume_tac)>>
                  gs[Excl "DATUM_mkDATUM"]>>qexists_tac‘mkDATUM v’>>
                  simp[]>>disj2_tac>>
                  simp[namespacePropsTheory.nsLookup_alist_to_ns_none]>>
                  gs[ALOOKUP_NONE,MEM_MAP,ZIP_MAP,LENGTH_MAP]>>rw[]>>
                  PairCases_on‘y’>>gs[]>>rveq>>
                  ‘LENGTH params = LENGTH vs'’
                    by (drule LIST_REL_LENGTH>>simp[LENGTH_MAP])>>
                  gs[MEM_ZIP]>>CCONTR_TAC>>gs[EL_MAP])))
      >- simp[cpFFI_valid_LTau_queue_eq]
      >- (rw []
          >- (first_x_assum irule>>
              gs[regexpTheory.LIST_UNION_def,
                 MEM_LIST_UNION,MEM_MAP,PULL_EXISTS]>>
              rveq>>irule_at Any ALOOKUP_MEM>>simp[]>>
              last_x_assum (irule_at Any)>>
              simp[closure_nodenames_def]>>
              disj2_tac>>simp[MEM_LIST_UNION]>>
              first_x_assum (irule_at Any)>>
              simp[MAP_MAP_o,MEM_MAP]>>
              metis_tac[])
          >- (first_x_assum irule>>
              gs[regexpTheory.LIST_UNION_def,
                 MEM_LIST_UNION,MEM_MAP,PULL_EXISTS]>>
              rveq>>irule_at Any ALOOKUP_MEM>>simp[]>>
              last_x_assum (irule_at Any)>>
              simp[closure_nodenames_def])))
QED

Definition transN_def:
  transN conf (ep0,pN0) (ep,pN) ⇔
    ∃L. trans conf ep0 L ep ∧ can_match conf pN0 L
End

Theorem trans_pres_letrec_closure:
  trans conf (NEndpoint p ps0 ep0) L (NEndpoint p ps ep) ∧
  letrec_endpoint ep0 ∧
  EVERY (letrec_closure o SND) ps0.funs ⇒
  EVERY (letrec_closure o SND) ps.funs ∧ letrec_endpoint ep
Proof
  Induct_on ‘trans’ >> simp[] >>
  rw[letrec_closure_def, letrec_endpoint_def]
  >- (pop_assum mp_tac >> simp[o_DEF, ELIM_UNCURRY])
  >- gs[choreoUtilsTheory.ALOOKUP_SOME_SPLIT, letrec_closure_def]
  >- gs[choreoUtilsTheory.ALOOKUP_SOME_SPLIT, letrec_closure_def]
  >- (gs[choreoUtilsTheory.ALOOKUP_SOME_SPLIT, letrec_closure_def] >>
      qpat_x_assum ‘EVERY (UNCURRY f) _’ mp_tac >>
      simp[o_DEF, ELIM_UNCURRY]) >>
  gs[choreoUtilsTheory.ALOOKUP_SOME_SPLIT, letrec_closure_def]
QED

Theorem NRC_same_start:
  (∀a b c. R a b ∧ R a c ⇒ b = c) ⇒
  NRC R m x y ∧ NRC R n x z ∧ m ≤ n ⇒
  NRC R (n - m) y z
Proof
  strip_tac >> map_every qid_spec_tac [‘x’, ‘y’, ‘z’, ‘n’] >>
  Induct_on ‘m’ >> simp[NRC] >> Cases_on ‘n’ >> simp[NRC] >>
  metis_tac[]
QED

Theorem stepr_det:
  ∀a b c. stepr a b ∧ stepr a c ⇒ b = c
Proof
  csimp[e_step_reln_def]
QED


Theorem simulated_stepr_pushes_forward:
  simR conf p0 cEnv0 pSt0 EP0 pN0 vs cvs cSt0 ∧
  (∀nd.
     nd ∈ network_nodenames (NEndpoint p0 pSt0 EP0) ⇒
     ffi_has_node nd cSt0.ffi.ffi_state) ∧ letrec_endpoint EP0 ∧
  EVERY (letrec_closure ∘ SND) pSt0.funs ∧ pletrec_vars_ok EP0 ∧
  EVERY cletrec_vars_ok (MAP SND pSt0.funs) ∧
  NRC stepr fn
      (cEnv0, (cSt0.refs,cSt0.ffi), Exp (compile_endpoint conf vs EP0), [])
      (ce, (cr,cf), cv, ck) ∧ cf.io_events = cSt0.ffi.io_events ∧
  NRC stepr n (ce, (cr,cf), cv, ck) c_ultimate
  ⇒
  ∃EP pN pSt cs cEnv cSt vs' m.
    RTC (transN conf) (NEndpoint p0 pSt0 EP0, pN0) (NEndpoint p0 pSt EP, pN) ∧
    simR conf p0 cEnv pSt EP pN vs' cvs cSt ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p0 pSt EP) ⇒
          ffi_has_node nd cSt.ffi.ffi_state) ∧ letrec_endpoint EP ∧
    EVERY (letrec_closure o SND) pSt.funs ∧ pletrec_vars_ok EP ∧
    EVERY cletrec_vars_ok (MAP SND pSt.funs) ∧
    stepr꙳ (cEnv, smSt cSt, Exp (compile_endpoint conf vs' EP), []) cs ∧
    NRC stepr m (cEnv0, smSt cSt0, Exp (compile_endpoint conf vs EP0), []) cs ∧
    (nf (transN conf) (NEndpoint p0 pSt EP, pN) ∧ m ≤ fn + n ∨ fn + n < m)
Proof
  map_every qid_spec_tac [‘cEnv0’, ‘pSt0’, ‘cSt0’, ‘EP0’, ‘vs’,
                          ‘ce’, ‘cr’, ‘cf’, ‘cv’, ‘ck’] >>
  ‘∃trip. trip = (n,fn,pN0)’ by simp[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [‘n’, ‘fn’, ‘pN0’, ‘trip’ ]>>
  ‘WF (prim_rec$< LEX prim_rec$< LEX measure outgoing_size)’ by simp[WF_LEX] >>
  dxrule_then (ho_match_mp_tac o SRULE [RIGHT_FORALL_IMP_THM])
             WF_INDUCTION_THM >>
  simp[FORALL_PROD] >> qx_genl_tac [‘n’, ‘fn’, ‘pN0’] >>
  disch_then (hide "IH") >> rpt strip_tac >>
  Cases_on ‘∃epN. transN conf (NEndpoint p0 pSt0 EP0, pN0) epN’ >> gs[]
  >- (PairCases_on ‘epN’ >> gs[transN_def] >>
      drule_then strip_assume_tac trans_struct_pres_NEndpoint >> gvs[] >>
      drule_then drule simulation >> simp[] >> impl_tac >- metis_tac[] >>
      disch_then $ qx_choosel_then [‘cEnv1’, ‘cSt1’, ‘pN1’, ‘vs1’, ‘stepc’]
                   strip_assume_tac >>
      drule_all_then strip_assume_tac letrec_vars_ok_trans_pres >>
      drule_all_then strip_assume_tac trans_pres_letrec_closure >>
      Cases_on ‘stepc = 0’
      >- (reverse (fs[triR_def, to_small_st_def]) >- fs[] >> gvs[] >>
          use_hidden_assum "IH" $ qspecl_then [‘n’, ‘fn’, ‘pN1’] mp_tac >>
          simp[LEX_DEF_THM] >> disch_then drule >> simp[] >>
          first_assum (disch_then o resolve_then Any mp_tac)>>
          first_assum (disch_then o resolve_then Any mp_tac)>>
          impl_tac >- metis_tac[] >>
          disch_then $ qx_choosel_then [‘EP2’, ‘pN2’, ‘pSt2’, ‘cs2’, ‘cEnv2’,
                                        ‘cSt2’, ‘vs2’, ‘m2’] strip_assume_tac
          >- (irule_at (Pos hd) (cj 2 RTC_RULES) >>
              first_assum $ irule_at (Pos (el 2)) >> simp[] >>
              gs[to_small_st_def] >>
              first_assum $ irule_at (Pos last) >> simp[transN_def] >>
              metis_tac[]) >>
          irule_at (Pos hd) (cj 2 RTC_RULES) >> gs[to_small_st_def] >>
          first_assum $ irule_at (Pos (el 2)) >> simp[transN_def] >>
          metis_tac[]) >>
      gs[triR_def, to_small_st_def] >> cheat) >> cheat (*

      >- (Cases_on ‘n < stepc’
          >- (irule_at Any RTC_SUBSET >> simp[transN_def] >>
              irule_at Any (DECIDE “p ⇒ q ∨ p”) >> first_assum $ irule_at Any >>
              first_assum $ irule_at (Pos last) >> metis_tac[RTC_REFL]) >>
          ‘stepc ≤ n’ by simp[] >>
          drule_all_then assume_tac (MATCH_MP NRC_same_start stepr_det) >>
          use_hidden_assum "IH" $ qspecl_then [‘n - stepc’, ‘pN1’] mp_tac >>
          simp[LEX_DEF_THM] >> simp[to_small_st_def] >>
          disch_then $ drule_at (Pos last) >>
          disch_then $ drule >> simp[] >> impl_tac >- metis_tac[] >>
          disch_then $ qx_choosel_then [‘EP2’, ‘pN2’, ‘pSt2’, ‘cs2’, ‘cEnv2’,
                                        ‘cSt2’, ‘vs2’, ‘m2’] strip_assume_tac
          >- (irule_at (Pos hd) (cj 2 RTC_RULES) >>
              first_assum $ irule_at (Pos (el 2)) >> simp[] >>
              irule_at Any NRC_ADD_I >> first_assum $ irule_at (Pos hd) >>
              first_assum $ irule_at (Pos hd) >> simp[transN_def] >>
              metis_tac[]) >>
          irule_at Any NRC_ADD_I >> first_assum $ irule_at (Pos hd) >>
          irule_at Any (cj 2 RTC_RULES) >>
          first_assum $ irule_at (Pos (el 2)) >> simp[transN_def] >>
          metis_tac[ADD_COMM]) >>
      (* case when c0 and c1 merge at c' *)
      *)

QED


       







Theorem NPar_trans_l_cases_full:
  ∀p s c s' c' conf n n'.
   trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n')
   ⇒ (s = s' ∧ c = c') ∨
     ∃L. trans conf (NEndpoint p s c) L (NEndpoint p s' c') ∧
         ((n' = n ∧ L = LTau) ∨
          (∃q d. trans conf n (LReceive p d q) n' ∧ L = LSend p d q) ∨
          (∃q d. trans conf n (LSend q d p) n'    ∧ L = LReceive q d p))
Proof
  rw []
  \\ qpat_x_assum `trans _ _ _ _` (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ rw []
  >- (disj2_tac \\ asm_exists_tac \\ fs []
      \\ qpat_x_assum `trans _ (NEndpoint _ _ _) _ _`
                      (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
      \\ rw [] \\ metis_tac [])
  >- (disj2_tac \\ asm_exists_tac \\ fs []
      \\ qpat_x_assum `trans _ (NEndpoint _ _ _) _ _`
                      (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
      \\ rw [] \\ metis_tac [])
  \\ metis_tac []
QED

Theorem NPar_trans_l_cases:
  ∀p s c s' c' conf n n'.
   trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n')
   ⇒ (s = s' ∧ c = c') ∨ ∃L. trans conf (NEndpoint p s c) L (NEndpoint p s' c')
Proof
  metis_tac [NPar_trans_l_cases_full]
QED

Theorem NPar_trans_r_cases:
  ∀conf n n' l l'.
   trans conf (NPar l n) LTau (NPar l' n')
   ⇒ (n = n') ∨ ∃L. trans conf n L n'
Proof
  rw []
  \\ qpat_x_assum `trans _ _ _ _` (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
  \\ rw []
  \\ metis_tac []
QED

Theorem trans_not_same:
  ∀conf n1 l n2 . trans conf n1 l n2 ∧ conf.payload_size > 0 ∧ l ≠ LTau ⇒ n1 ≠ n2
Proof
  rpt gen_tac \\ strip_tac
  \\ rpt (pop_assum mp_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [‘n2’,‘l’,‘n1’,‘conf’]
  \\ ho_match_mp_tac trans_strongind \\ rw []
  >- (spose_not_then (strip_assume_tac o AP_TERM “endpoint_size”) >>
      gvs[endpoint_size_def])
  >- rw [payloadLangTheory.state_component_equality]
QED

Theorem trans_ffi_eq_same:
  ∀p s c conf n n'.
   ffi_wf (p,s.queues,n) ∧
   conf.payload_size > 0 ∧
   trans conf (NPar (NEndpoint p s c) n ) LTau
              (NPar (NEndpoint p s c) n')
   ⇒ ffi_eq conf (p,s.queues,n) (p,s.queues,n')
Proof
  rw []
  \\ irule internal_trans_equiv_irrel
  \\ fs [ffi_wf_def]
  \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [trans_cases]) \\ fs []
  \\ irule RTC_SINGLE
  \\ fs [internal_trans_def]
  \\ ntac 2 (last_x_assum (K ALL_TAC))
  \\ IMP_RES_TAC trans_not_same \\ rw [] \\ fs []
QED

Theorem LIST_TYPE_WORD_EXISTS:
 ∀xs:word8 list. ∃v. LIST_TYPE WORD xs v
Proof
 Induct \\ fs [LIST_TYPE_def,WORD_def]
 \\ goal_assum (first_assum o mp_then Any mp_tac)
QED

Theorem endpoint_trans_tau_IMP_strans:
  trans conf (NEndpoint p s c) LTau (NEndpoint p s' c') ⇒
  ((p,s.queues,n) = (p,s'.queues,n)) ∨
  ∃L. strans conf (p,s.queues,n) L (p,s'.queues,n)
Proof
  rw[Once trans_cases] >> rw[] >>
  disj2_tac >>
  irule_at Any (cj 1 strans_rules) >>
  metis_tac[]
QED

Theorem normalise_queues_add_same:
  normalise_queues (q |+ (p,qlk q p)) =
  normalise_queues q
Proof
  rw[fmap_eq_flookup,FLOOKUP_normalise_queues_FUPDATE] >> rw[] >>
  gvs[qlk_def,fget_def,AllCaseEqs(),FLOOKUP_normalise_queues] >>
  Cases_on ‘FLOOKUP q p’ >> gvs[]
QED

Theorem ffi_eq_cpFFI_valid_pres:
  trans conf (NEndpoint p s c) LTau (NEndpoint p s' c') ∧
  normalised s.queues ∧
  ffi_wf (p,s.queues,n) ∧
  cpFFI_valid conf s s' (p,s.queues,n) st1 LTau ⇒
  ffi_eq conf st1 (p,s'.queues,n)
Proof
  simp[cpFFI_valid_def,some_def] >>
  reverse IF_CASES_TAC
  >- (simp[] >>
      strip_tac >>
      ‘s'.queues = s.queues’
        suffices_by metis_tac[ffi_eq_equivRel,equivalence_def,symmetric_def] >>
      gvs[EXISTS_PROD,FORALL_PROD] >>
      gvs[Once trans_cases] >>
      spose_not_then kall_tac >>
      last_x_assum(qspecl_then [‘p1’,‘d’] mp_tac) >>
      simp[] >>
      gvs[normalised_def,normalise_queues_FUPDATE_NONEMPTY] >>
      rw[fmap_eq_flookup,FLOOKUP_UPDATE] >> rw[] >>
      gvs[qlk_def,fget_def,AllCaseEqs()])
  >- (SELECT_ELIM_TAC >>
      conj_tac >- metis_tac[] >>
      pop_assum kall_tac >>
      simp[FORALL_PROD] >>
      rw[] >>
      gvs[Once trans_cases,payloadLangTheory.state_component_equality]
      >- (PairCases_on ‘st1’ >>
          imp_res_tac strans_pres_pnum >>
          gvs[] >>
          match_mp_tac ffi_eq_pres >>
          irule_at Any ffi_eq_REFL >>
          qhdtm_x_assum ‘strans’ (irule_at Any) >>
          simp[] >>
          rename1 ‘ARecv pp1 dd’ >>
          ‘pp1 = p1 ∧ dd = d’
            by(gvs[fmap_eq_flookup] >>
               qpat_x_assum ‘∀x. FLOOKUP (normalise_queues _) _ = _’ (qspec_then ‘p1’ mp_tac) >>
               simp[FLOOKUP_normalise_queues,FLOOKUP_UPDATE] >>
               rw[] >>
               gvs[qlk_def,fget_def,AllCaseEqs()]) >>
          rveq >>
          match_mp_tac (cj 1 strans_rules) >>
          simp[])
      >- (PairCases_on ‘st1’ >>
          imp_res_tac strans_pres_pnum >>
          gvs[] >>
          match_mp_tac ffi_eq_pres >>
          irule_at Any ffi_eq_REFL >>
          qhdtm_x_assum ‘strans’ (irule_at Any) >>
          simp[] >>
          rename1 ‘ARecv pp1 dd’ >>
          ‘pp1 = p1 ∧ dd = d’
            by(gvs[fmap_eq_flookup] >>
               qpat_x_assum ‘∀x. FLOOKUP (normalise_queues _) _ = _’ (qspec_then ‘p1’ mp_tac) >>
               simp[FLOOKUP_normalise_queues,FLOOKUP_UPDATE] >>
               rw[] >>
               gvs[qlk_def,fget_def,AllCaseEqs()]) >>
          rveq >>
          match_mp_tac (cj 1 strans_rules) >>
          simp[]) >>
      gvs[fmap_eq_flookup] >>
      rename1 ‘ARecv pp1 dd’ >>
      qpat_x_assum ‘∀x. FLOOKUP (normalise_queues _) _ = _’ (qspec_then ‘pp1’ mp_tac) >>
      gvs[FLOOKUP_normalise_queues,FLOOKUP_UPDATE,qlk_def,fget_def] >>
      PURE_TOP_CASE_TAC >> simp[])
QED

Theorem network_NPar_forward_correctness:
  ∀conf s c n p s' c' n' cSt0 vs cvs env0.
  trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n') ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd cSt0.ffi.ffi_state) ∧
  cpEval_valid conf p env0 s c n vs cvs cSt0 ∧
  letrec_network (NPar (NEndpoint p s c) n) ∧
  cSt0.ffi.ffi_state = (p,s.queues,n) ∧
  pletrec_vars_ok c ∧
  EVERY cletrec_vars_ok (MAP SND s.funs) ∧
  normalised s.queues
  ⇒
  ∃env cSt vs2 sc.
    triR stepr sc
         (env0, smSt cSt0, Exp (compile_endpoint conf vs c), [])
         (env, smSt cSt, Exp (compile_endpoint conf vs2 c'), []) ∧
    cpEval_valid conf p env s' c' n' vs2 cvs cSt ∧
    ffi_eq conf cSt.ffi.ffi_state (p,s'.queues,n') ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p s' c') ⇒ ffi_has_node nd cSt.ffi.ffi_state)
Proof
  rw [] >>
  drule_then assume_tac NPar_trans_l_cases_full >>
  fs [] >> rveq
  (* p is not involved at all *)
  >- (irule_at (Pos hd) triR_REFL >>
      gvs[cpEval_valid_def,ffi_state_cor_def] >>
      drule trans_ffi_eq_same >>
      disch_then(drule_at (Pos last)) >>
      rw[] >>
      gvs[Once trans_cases] >>
      metis_tac[trans_pres_ffi_wf])
  (* LTau (only p does something) *)
  >- (drule simulation >>
      simp[wfLabel_def] >>
      disch_then drule >>
      impl_tac
      >- (gs[DISJ_IMP_THM,FORALL_AND_THM,can_match_def,
             letrec_network_def,endpoints_def,o_DEF,
             ELIM_UNCURRY]) >>
      rpt strip_tac >>
      goal_assum drule >>
      simp[] >>
      rpt(reverse conj_tac) >- metis_tac[]
      >- (match_mp_tac ffi_eq_cpFFI_valid_pres >>
          gvs[cpEval_valid_def]) >>
      gvs[cpEval_valid_def] >>
      Cases_on ‘cSt.ffi.ffi_state’ >> Cases_on ‘r’ >> gvs[ffi_state_cor_def] >>
      drule ffi_eq_cpFFI_valid_pres >>
      disch_then drule_all >>
      strip_tac >>
      simp[] >>
      gvs[ffi_wf_def])
   (* LSend *)
  >- (drule simulation >>
      simp[wfLabel_def] >>
      disch_then drule >>
      impl_tac
      >- (gs[DISJ_IMP_THM,FORALL_AND_THM,can_match_def,
             letrec_network_def,endpoints_def,o_DEF,
             ELIM_UNCURRY]) >>
      rpt strip_tac >>
      goal_assum drule >>
      simp[] >>
      rpt(reverse conj_tac) >- metis_tac[] >>
      simp[] >>
      gvs[cpFFI_valid_def] >>
      drule (strans_rules |> CONJUNCTS |> last) >>
      disch_then (qspec_then ‘s.queues’ mp_tac) >>
      strip_tac >>
      ‘s'.queues = s.queues’
        by(qpat_x_assum ‘trans _ _ (LSend _ _ _) _’ mp_tac >>
           rw[Once trans_cases]) >>
      gvs[]
      >- (match_mp_tac ffi_eq_pres
          \\ first_x_assum(irule_at (Pos last))
          \\ first_x_assum(irule_at (Pos last))
          \\ simp[]
          \\ gvs[cpEval_valid_def]) >>
      gvs[cpEval_valid_def] \\
      Cases_on ‘cSt.ffi.ffi_state’ \\ Cases_on ‘r’ >> gvs[ffi_state_cor_def] >>
      imp_res_tac strans_pres_wf >>
      simp[] >>
      match_mp_tac ffi_eq_pres >>
      first_x_assum(irule_at (Pos last)) >>
      first_x_assum(irule_at (Pos last)) >>
      simp[] >>
      gvs[cpEval_valid_def])
   (* LReceive *)
  >- (drule simulation >>
      imp_res_tac trans_wfLabel >>
      simp[] >>
      disch_then drule >>
      impl_tac
      >- (gs[DISJ_IMP_THM,FORALL_AND_THM,can_match_def,
             letrec_network_def,endpoints_def,o_DEF,
             ELIM_UNCURRY]) >>
      rpt strip_tac >>
      goal_assum drule >>
      simp[] >>
      gs[DISJ_IMP_THM,FORALL_AND_THM] >>
      gvs[cpEval_valid_def] >>
      Cases_on ‘cSt.ffi.ffi_state’ >> Cases_on ‘r’ >> gvs[ffi_state_cor_def] >>
      gvs[AC CONJ_SYM CONJ_ASSOC] >>
      conj_asm1_tac >- drule_all_then MATCH_ACCEPT_TAC trans_pres_ffi_wf >>
      gvs[cpFFI_valid_def] >>
      qpat_x_assum ‘trans _ _ (LReceive _ _ _) _’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >>
      gvs[] >>
      dxrule_then assume_tac (iffLR ffi_eq_SYM) >>
      drule_then match_mp_tac ffi_eq_TRANS >>
      match_mp_tac active_trans_equiv_irrel >>
      conj_tac >- gvs[cpEval_valid_def] >>
      match_mp_tac RTC_SUBSET >>
      simp[active_trans_def,emit_trans_def])
QED

(* TODO: move *)
Theorem smallstep_oracle_invariant:
  stepr (env, st, e, l) (env', st', e', l') ⇒
  (SND st').oracle = (SND st).oracle
Proof
  PairCases_on ‘st’ >>
  rw[e_step_reln_def,e_step_def,AllCaseEqs(),smallStepTheory.push_def,smallStepTheory.return_def,
     continue_def] >>
  gvs[application_def,AllCaseEqs(),do_opapp_def,return_def] >>
  gvs[do_app_def,call_FFI_def,AllCaseEqs(),ELIM_UNCURRY]
QED

Theorem smallsteps_oracle_invariant:
  stepr꙳ (env, st, e, l) (env', st', e', l') ⇒
  (SND st').oracle = (SND st).oracle
Proof
  Cases_on ‘st’ >> Cases_on ‘st'’ >> gvs[] >> strip_tac >>
  CONV_TAC SYM_CONV >>
  qspecl_then [‘λx. (SND(FST(SND x))).oracle’,‘stepr’] (match_mp_tac o SIMP_RULE (srw_ss()) [FORALL_PROD]) (MP_CANON(GEN_ALL RTC_lifts_equalities)) >>
  first_x_assum(irule_at Any) >>
  rpt strip_tac >>
  drule smallstep_oracle_invariant >>
  simp[]
QED

Theorem ffi_irrel_smallstep:
  ffi_eq conf cSt.ffi.ffi_state ffi2 ∧ ffi_wf cSt.ffi.ffi_state ∧ ffi_wf ffi2 ∧
  cSt.ffi.oracle = comms_ffi_oracle conf ∧
  stepr (env, smSt cSt, e, l) (env', smSt cSt', e', l') ⇒
  ∃ffi3. stepr (env, smSt(cSt with ffi := (cSt.ffi with ffi_state := ffi2)), e, l)
               (env', smSt(cSt' with ffi := (cSt'.ffi with ffi_state := ffi3)), e', l') ∧
         ffi_wf ffi3 ∧ ffi_wf cSt'.ffi.ffi_state ∧
         ffi_eq conf cSt'.ffi.ffi_state ffi3
Proof
  rw[e_step_reln_def,e_step_def,AllCaseEqs(),smallStepTheory.push_def,smallStepTheory.return_def,
     continue_def] >>
  gvs[to_small_st_def,semanticPrimitivesTheory.state_component_equality,ffi_state_component_equality]
  >- (gvs[application_def,AllCaseEqs(),do_app_def,do_opapp_def])
  >- (gvs[application_def,AllCaseEqs(),do_app_def,do_opapp_def])
  >- (qpat_x_assum ‘_ = ssstep _’ (strip_assume_tac o REWRITE_RULE[application_def]) >>
      gvs[AllCaseEqs(),return_def] >>
      gvs[do_app_def,AllCaseEqs(),application_def,return_def,semanticPrimitivesTheory.state_component_equality,ffi_state_component_equality,ELIM_UNCURRY] >>
      gvs[call_FFI_def,AllCaseEqs(),PULL_EXISTS] >>
      qpat_x_assum ‘comms_ffi_oracle _ = _’ (assume_tac o GSYM) >>
      gvs[comms_ffi_oracle_def,ffi_send_def,ffi_receive_def] >>
      rw[] >> gvs[]
      >- (gvs[ffi_send_def,AllCaseEqs()] >>
          gvs[some_def] >>
          conj_tac
          >- (gvs[ffi_eq_def, Once bisimulationTheory.BISIM_REL_cases] >>
              metis_tac[]) >>
          SELECT_ELIM_TAC >>
          conj_tac
          >- (gvs[ffi_eq_def, Once bisimulationTheory.BISIM_REL_cases] >>
              metis_tac[]) >>
          rw[]
          >- metis_tac[strans_pres_wf]
          >- metis_tac[strans_pres_wf]
          >- metis_tac[ffi_eq_pres])
      >- (gvs[ffi_receive_def,AllCaseEqs()] >>
          gvs[some_def] >>
          gvs[ELIM_UNCURRY] >>
          first_x_assum(irule_at (Pat ‘store_assign _ _ _ = _’)) >>
          qhdtm_assum ‘ffi_eq’ (strip_assume_tac o REWRITE_RULE[ffi_eq_def, Once bisimulationTheory.BISIM_REL_cases]) >>
          gvs[FORALL_AND_THM] >>
          first_x_assum drule_all >>
          strip_tac >>
          simp[Once EXISTS_PROD] >>
          first_assum(irule_at (Pos hd)) >>
          SELECT_ELIM_TAC >>
          conj_tac >- (simp[Once EXISTS_PROD] >> metis_tac[]) >>
          rw[] >>
          qpat_x_assum ‘$@ _ = _’ mp_tac >>
          SELECT_ELIM_TAC >>
          conj_tac >- metis_tac[] >>
          rpt strip_tac >>
          imp_res_tac functional_ARecv >>
          rveq >>
          rename1 ‘tup = (_,_)’ >>
          Cases_on ‘tup’ >>
          simp[] >>
          fs[] >> rveq >>
          metis_tac[ffi_eq_pres,strans_pres_wf]))
QED

Theorem ffi_irrel_smallsteps:
  ∀conf cSt ffi2 env e l env' cSt' e' l'.
  ffi_eq conf cSt.ffi.ffi_state ffi2 ∧ ffi_wf cSt.ffi.ffi_state ∧ ffi_wf ffi2 ∧
  cSt.ffi.oracle = comms_ffi_oracle conf ∧
  stepr꙳ (env, smSt cSt, e, l) (env', smSt cSt', e', l') ⇒
  ∃ffi3. stepr꙳ (env, smSt(cSt with ffi := (cSt.ffi with ffi_state := ffi2)), e, l)
               (env', smSt(cSt' with ffi := (cSt'.ffi with ffi_state := ffi3)), e', l') ∧
         ffi_wf ffi3 ∧ ffi_wf cSt'.ffi.ffi_state ∧
         ffi_eq conf cSt'.ffi.ffi_state ffi3
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac ‘RTC _ f1 f2’ >>
  ntac 2 (pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE[markerTheory.Abbrev_def])) >>
  rpt(last_x_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`cSt`,`ffi2`,`env`,`e`,`l`,`env'`,`cSt'`,`e'`,`l'`,‘f2’,‘f1’] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[]
  >- (gvs[to_small_st_def] >>
      irule_at (Pos hd) RTC_REFL >>
      simp[])
  >- (rename1 ‘stepr _ sst’ >>
      PairCases_on ‘sst’ >>
      ‘∃s. (sst1,sst2) = smSt s’
        by(rw[to_small_st_def] >>
           qexists_tac ‘<|refs := sst1; ffi := sst2|>’ >> simp[]) >>
      drule ffi_irrel_smallstep >>
      rpt(disch_then drule) >>
      disch_then (mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev)) >>
      gvs[] >>
      disch_then drule >>
      strip_tac >>
      irule_at (Pos hd) (cj 2 RTC_rules) >>
      first_x_assum (irule_at (Pos hd)) >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      simp[] >>
      drule smallstep_oracle_invariant >>
      rw[to_small_st_def])
QED

Theorem steprs_ffi_wf:
  stepr꙳ (env,st,e,l) (env',st',e',l') ∧
  (SND st).oracle = comms_ffi_oracle conf ∧
  ffi_wf (SND st).ffi_state ⇒
  ffi_wf (SND st').ffi_state
Proof
  rpt strip_tac >>
  qspecl_then [‘conf’,
               ‘<| refs := FST st; ffi := SND st|>’,
               ‘(SND st).ffi_state’,
               ‘env’,
               ‘e’,
               ‘l’,
               ‘env'’,
               ‘<| refs := FST st'; ffi := SND st'|>’
               ] assume_tac ffi_irrel_smallsteps >>
  gvs[to_small_st_def] >>
  pop_assum drule >>
  rw[]
QED

Theorem steprs_ffi_wf':
  stepr꙳ (env,(refs,st),e,l) (env',(refs',st'),e',l') ∧
  st.oracle = comms_ffi_oracle conf ∧
  ffi_wf st.ffi_state ⇒
  ffi_wf st'.ffi_state
Proof
  rpt strip_tac >>
  drule steprs_ffi_wf >>
  metis_tac[FST,SND]
QED

Theorem EP_nodenames_dsubst_lemma:
  ∀e dn e'.
  x ∈ EP_nodenames (dsubst e dn e') ⇒
  x ∈ EP_nodenames e ∨ x ∈ EP_nodenames e'
Proof
 rpt strip_tac >> Induct_on ‘e’ >>
 rw[dsubst_def] >>
 res_tac >> rw[]
QED

(* TODO: Curtis Mayfield *)
Theorem trans_network_nodenames_mono:
  ∀conf n1 α n2. trans conf n1 α n2 ⇒ network_nodenames n2 ⊆ network_nodenames n1
Proof
  ho_match_mp_tac trans_ind >>
  rw[SUBSET_DEF,MEM_LIST_UNION,MEM_MAP,PULL_EXISTS] >> simp[] >>
  imp_res_tac EP_nodenames_dsubst_lemma >>
  gvs[MEM_LIST_UNION,MEM_MAP,PULL_EXISTS] >>
  drule_then (irule_at (Pos hd)) ALOOKUP_MEM >>
  simp[MEM_LIST_UNION,MEM_MAP,PULL_EXISTS]
QED

Theorem trans_network_nodenames_mono_NPar:
  ∀conf n1 n2 α n1' n2'.
    trans conf (NPar n1 n2) α (NPar n1' n2') ⇒ network_nodenames n1' ⊆ network_nodenames n1 ∧ network_nodenames n2' ⊆ network_nodenames n2
Proof
  rw[Once trans_cases] >>
  imp_res_tac trans_network_nodenames_mono >> simp[]
QED

Theorem network_NPar_forward_correctness':
  ∀conf s c n p s' c' n' cSt0 vs cvs env0.
  trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n') ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd cSt0.ffi.ffi_state) ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd (p,s.queues,n)) ∧
  letrec_network (NPar (NEndpoint p s c) n) ∧
  cpEval_valid conf p env0 s c n vs cvs cSt0 ∧
  ffi_eq conf cSt0.ffi.ffi_state (p,s.queues,n) ∧
  ffi_wf (p,s.queues,n) ∧
  pletrec_vars_ok c ∧
  EVERY cletrec_vars_ok (MAP SND s.funs) ∧
  normalised s.queues
  ⇒
  ∃env cSt env' e' l' sst sst' vs'.
    stepr꙳
      (env0, smSt cSt0, Exp (compile_endpoint conf vs c), [])
      (env', sst, e', l') ∧
    stepr꙳
      (env, smSt cSt, Exp (compile_endpoint conf vs' c'), [])
      (env', sst', e', l') ∧
    ffi_eq conf (SND sst).ffi_state (SND sst').ffi_state ∧
    cpEval_valid conf p env s' c' n' vs' cvs cSt ∧
    ffi_eq conf cSt.ffi.ffi_state (p,s'.queues,n') ∧
    FST sst = FST sst' ∧
    (SND sst).oracle = (SND sst').oracle ∧
    (SND sst).io_events = (SND sst').io_events ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p s' c') ⇒ ffi_has_node nd cSt.ffi.ffi_state)
Proof
  rpt strip_tac >>
  drule_at (Pos last) network_NPar_forward_correctness >>
  disch_then (drule_at (Pos last)) >>
  disch_then drule >>
  disch_then(qspec_then ‘cSt0 with ffi := (cSt0.ffi with ffi_state := (p,s.queues,n))’ mp_tac) >>
  simp[] >>
  disch_then(qspecl_then [‘vs’,‘cvs’,‘env0’] mp_tac) >>
  impl_tac
  >- (gvs[cpEval_valid_def, ffi_state_cor_def]) >>
  strip_tac >>
  gvs[triR_def] >>
  rename1 ‘RTC _ _ sst’ >>
  PairCases_on ‘sst’ >>
  ‘∃s. (sst1,sst2) = smSt s’
    by(rw[to_small_st_def] >>
       qexists_tac ‘<|refs := sst1; ffi := sst2|>’ >> simp[]) >>
  gvs[] >>
  drule_at (Pos last) ffi_irrel_smallsteps >>
  simp[] >>
  imp_res_tac ffi_eq_SYM >>
  disch_then drule >>
  impl_tac
  >- (gvs[cpEval_valid_def]) >>
  qmatch_goalsub_abbrev_tac ‘smSt a1’ >>
  ‘a1 = cSt0’
    by(rw[Abbr ‘a1’,semanticPrimitivesTheory.state_component_equality,
          ffi_state_component_equality]) >>
  gvs[Abbr ‘a1’] >>
  pop_assum kall_tac >>
  strip_tac >>
  simp[PULL_EXISTS] >>
  first_assum(irule_at (Pos hd)) >>
  last_assum(fn thm => mp_then (Pos last) mp_tac ffi_irrel_smallsteps thm) >>
  disch_then drule >>
  impl_tac
  >- (gvs[cpEval_valid_def] >>
      gvs[Once trans_cases] >>
      metis_tac[ffi_wf_def,trans_pres_ffi_wf]) >>
  strip_tac >>
  first_x_assum(irule_at (Pos hd)) >>
  simp[to_small_st_def] >>
  conj_tac >- metis_tac[ffi_eq_SYM,ffi_eq_TRANS] >>
  conj_tac
  >- (gvs[cpEval_valid_def] >> gvs[ffi_state_cor_thm]) >>
  drule trans_network_nodenames_mono_NPar >>
  simp[SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM] >>
  rw[] >>
  res_tac >>
  gvs[ffi_has_node_def,net_has_node_MEM_endpoints] >>
  imp_res_tac endpoint_names_trans >>
  gvs[endpoints_def]
QED

Theorem network_NPar_forward_correctness'':
  ∀conf s c n p s' c' n' cSt0 vs cvs env0.
  trans conf (NPar (NEndpoint p s c) n) LTau (NPar (NEndpoint p s' c') n') ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd cSt0.ffi.ffi_state) ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd (p,s.queues,n)) ∧
  cpEval_valid conf p env0 s c n vs cvs cSt0 ∧
  letrec_network (NPar (NEndpoint p s c) n) ∧
  ffi_eq conf cSt0.ffi.ffi_state (p,s.queues,n) ∧
  ffi_wf (p,s.queues,n) ∧
  pletrec_vars_ok c ∧
  EVERY cletrec_vars_ok (MAP SND s.funs) ∧
  normalised s.queues
  ⇒
  ∃env cSt env' e' l' sst sst' vs'.
    stepr꙳
      (env0, smSt cSt0, Exp (compile_endpoint conf vs c), [])
      (env', sst, e', l') ∧
    stepr꙳
      (env, smSt cSt, Exp (compile_endpoint conf vs' c'), [])
      (env', sst', e', l') ∧
    ffi_eq conf (SND sst).ffi_state (SND sst').ffi_state ∧
    FST sst = FST sst' ∧
    (SND sst).oracle = (SND sst').oracle ∧
    (SND sst).io_events = (SND sst').io_events ∧
    cpEval_valid conf p env s' c' n' vs' cvs cSt ∧
    cSt.ffi.ffi_state = (p,s'.queues,n') ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p s' c') ⇒ ffi_has_node nd cSt.ffi.ffi_state)
Proof
  rpt strip_tac >>
  drule_all network_NPar_forward_correctness' >>
  strip_tac >>
  first_x_assum(irule_at (Pos hd)) >>
  drule ffi_irrel_smallsteps >>
  PairCases_on ‘sst'’ >>
  ‘∃s. (sst'0,sst'1) = smSt s’
    by(rw[to_small_st_def] >>
       qexists_tac ‘<|refs := sst'0; ffi := sst'1|>’ >> simp[]) >>
  gvs[] >>
  disch_then(drule_at (Pos last)) >>
  impl_tac
  >- (gvs[cpEval_valid_def, ffi_state_cor_def] >>
      gvs[Once trans_cases] >>
      metis_tac[ffi_wf_def,trans_pres_ffi_wf]) >>
  strip_tac >>
  first_x_assum(irule_at (Pos hd)) >>
  gvs[to_small_st_def] >>
  conj_tac >- metis_tac[ffi_eq_SYM,ffi_eq_TRANS] >>
  conj_tac
  >- (gvs[cpEval_valid_def,ffi_state_cor_thm,PULL_EXISTS] >>
      irule_at (Pos hd) ffi_eq_REFL >>
      gvs[Once trans_cases] >>
      metis_tac[ffi_wf_def,trans_pres_ffi_wf]) >>
  drule trans_network_nodenames_mono_NPar >>
  simp[SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM] >>
  rw[] >>
  res_tac >>
  gvs[ffi_has_node_def,net_has_node_MEM_endpoints] >>
  imp_res_tac endpoint_names_trans >>
  gvs[endpoints_def]
QED

Theorem stepr_cut_paste:
  ∀s1 s2 s3.
  stepr꙳ s1 s2 ∧ stepr꙳ s1 s3 ⇒
  s2 = s3 ∨
  stepr꙳ s2 s3 ∨
  stepr꙳ s3 s2
Proof
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[]
  >- (rw[] >>
      qpat_x_assum ‘RTC stepr s1 s3’ (strip_assume_tac o REWRITE_RULE[Once RTC_cases]) >>
      gvs[]
      >- metis_tac[RTC_rules] >>
      gvs[e_step_reln_def])
QED

Theorem network_NPar_forward_correctness_reduction_lemma:
  ∀conf s c n p s' c' n' cSt0 vs cvs env0.
  (reduction conf)꙳ (NPar (NEndpoint p s c) n) (NPar (NEndpoint p s' c') n') ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd cSt0.ffi.ffi_state) ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd (p,s.queues,n)) ∧
  cpEval_valid conf p env0 s c n vs cvs cSt0 ∧
  letrec_network (NPar (NEndpoint p s c) n) ∧
  ffi_eq conf cSt0.ffi.ffi_state (p,s.queues,n) ∧
  ffi_wf (p,s.queues,n) ∧
  pletrec_vars_ok c ∧
  EVERY cletrec_vars_ok (MAP SND s.funs) ∧
  normalised s.queues
  ⇒
  ∃env cSt env' e' l' sst sst' vs'.
    stepr꙳
      (env0, smSt cSt0, Exp (compile_endpoint conf vs c), [])
      (env', sst, e', l') ∧
    stepr꙳
      (env, smSt cSt, Exp (compile_endpoint conf vs' c'), [])
      (env', sst', e', l') ∧
    ffi_eq conf (SND sst).ffi_state (SND sst').ffi_state ∧
    FST sst = FST sst' ∧
    (SND sst).oracle = (SND sst').oracle ∧
    (SND sst).io_events = (SND sst').io_events ∧
    cpEval_valid conf p env s' c' n' vs' cvs cSt ∧
    cSt.ffi.ffi_state = (p,s'.queues,n') ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p s' c') ⇒ ffi_has_node nd cSt.ffi.ffi_state)
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac ‘RTC _ n1 n2’ >>
  ntac 2 (pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])) >>
  rpt(pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`s`,`c`,`n`,`p`,`s'`,`c'`,`n'`,`cSt0`,`vs`,`cvs`,`env0`,‘n2’,‘n1’] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rpt strip_tac >> rveq
  >- (gvs[triR_def,PULL_EXISTS,GSYM CONJ_ASSOC] >>
      ntac 2 (irule_at (Pos hd) RTC_REFL) >>
      simp[to_small_st_def] >>
      qexists_tac ‘cSt0 with ffi := (cSt0.ffi with ffi_state := (p,s.queues,n))’ >>
      gvs[cpEval_valid_def] >>
      simp[ffi_state_cor_def] >>
      metis_tac[])
  >- (gvs[reduction_def] >>
      rename1 ‘trans _ _ _ nn’ >>
      ‘∃s' c' n'. nn = NPar (NEndpoint p s' c') n'’
        by(gvs[Once trans_cases] >>
           imp_res_tac trans_struct_pres_NEndpoint >> gvs[]) >>
      rveq >>
      drule network_NPar_forward_correctness'' >>
      disch_then(qspec_then ‘cSt0’ mp_tac) >>
      simp[] >>
      disch_then drule >>
      disch_then drule >>
      disch_then drule >>
      strip_tac >>
      gvs[DISJ_IMP_THM,FORALL_AND_THM] >>
      last_x_assum(drule_at (Pat ‘cpEval_valid _ _ _ _ _ _ _ _’)) >>
      impl_tac
      >- (simp[] >>
          conj_tac >- metis_tac[letrec_network_trans_pres] >>
          conj_tac >- (gvs[Once trans_cases] >> metis_tac[ffi_wf_def,trans_pres_ffi_wf]) >>
          conj_tac >- (gvs[Once trans_cases] >> metis_tac[letrec_vars_ok_trans_pres]) >>
          conj_tac >- (gvs[Once trans_cases] >> metis_tac[letrec_vars_ok_trans_pres]) >>
          gvs[Once trans_cases] >>
          imp_res_tac payload_trans_normalised >>
          gvs[normalised_network_def]) >>
      strip_tac >>
      qpat_x_assum ‘RTC stepr (env,smSt cSt,_,_) _’ mp_tac >>
      disch_then (fn thm => mp_then (Pos hd) drule stepr_cut_paste thm >> assume_tac thm) >>
      strip_tac
      >- (simp[] >>
          first_x_assum (irule_at (Pos hd)) >>
          gvs[] >>
          first_x_assum(irule_at (Pos hd)) >>
          simp[] >>
          metis_tac[ffi_eq_TRANS,ffi_eq_SYM])
      >- (first_assum (irule_at (Pos hd)) >>
          irule_at (Pos hd) RTC_RTC >>
          first_assum (irule_at (Pos hd)) >>
          rename1 ‘RTC stepr (_,ssta,_,_) (_,sstb,_,_)’ >>
          MAP_EVERY PairCases_on [‘ssta’,‘sstb’] >>
          gvs[] >>
          ‘∃s1. (FST sst''',ssta1) = smSt s1’
            by(rw[to_small_st_def] >>
               qexists_tac ‘<|refs := FST sst'''; ffi := ssta1|>’ >> simp[]) >>
          ‘∃s2. (FST sst,sstb1) = smSt s2’
            by(rw[to_small_st_def] >>
               qexists_tac ‘<|refs := FST sst; ffi := sstb1|>’ >> simp[]) >>
          gvs[] >>
          drule_at (Pos last) ffi_irrel_smallsteps >>
          gvs[to_small_st_def] >>
          disch_then drule >>
          impl_tac
          >- (conj_asm1_tac
              >- (drule_then match_mp_tac steprs_ffi_wf' >>
                  gvs[cpEval_valid_def] >> metis_tac[]) >>
              conj_asm1_tac
              >- (drule_then match_mp_tac steprs_ffi_wf >>
                  simp[] >>
                  gvs[cpEval_valid_def] >> metis_tac[]) >>
              imp_res_tac smallsteps_oracle_invariant >>
              gvs[cpEval_valid_def]) >>
          strip_tac >>
          gvs[] >>
          irule_at (Pos hd) RTC_RTC >>
          irule_at (Pos hd) (METIS_PROVE [RTC_REFL] “∀R A B. A = B ⇒ RTC R A B”) >>
          first_x_assum(irule_at (Pat ‘RTC _ _ _’)) >>
          simp[] >>
          Cases_on ‘sst'''’ >> gvs[ffi_state_component_equality] >>
          metis_tac[ffi_eq_TRANS,ffi_eq_SYM])
      >- (irule_at (Pos hd) RTC_RTC >>
          first_assum (irule_at (Pos hd)) >>
          rename1 ‘RTC stepr (_,ssta,_,_) (_,sstb,_,_)’ >>
          MAP_EVERY PairCases_on [‘ssta’,‘sstb’] >>
          gvs[] >>
          ‘∃s1. (FST sst,ssta1) = smSt s1’
            by(rw[to_small_st_def] >>
               qexists_tac ‘<|refs := FST sst; ffi := ssta1|>’ >> simp[]) >>
          ‘∃s2. (FST sst''',sstb1) = smSt s2’
            by(rw[to_small_st_def] >>
               qexists_tac ‘<|refs := FST sst'''; ffi := sstb1|>’ >> simp[]) >>
          gvs[] >>
          drule_at (Pos last) ffi_irrel_smallsteps >>
          gvs[to_small_st_def] >>
          imp_res_tac ffi_eq_SYM >>
          disch_then drule >>
          impl_tac >-
            (conj_asm1_tac
             >- (drule_then match_mp_tac steprs_ffi_wf' >>
                 gvs[cpEval_valid_def] >> metis_tac[]) >>
             conj_asm1_tac
             >- (drule_then match_mp_tac steprs_ffi_wf >>
                 simp[] >>
                 gvs[cpEval_valid_def] >> metis_tac[]) >>
             imp_res_tac smallsteps_oracle_invariant >>
             gvs[cpEval_valid_def]) >>
          strip_tac >>
          gvs[] >>
          irule_at (Pos hd) RTC_RTC >>
          irule_at (Pos hd) (METIS_PROVE [RTC_REFL] “∀R A B. A = B ⇒ RTC R A B”) >>
          first_x_assum(irule_at (Pat ‘RTC _ _ _’)) >>
          simp[] >>
          Cases_on ‘sst’ >> gvs[ffi_state_component_equality] >>
          first_x_assum(irule_at (Pos hd)) >>
          simp[] >>
          metis_tac[ffi_eq_TRANS,ffi_eq_SYM]))
QED

Theorem network_NPar_forward_correctness_reduction:
  ∀conf s c n p s' c' n' cSt0 vs cvs env0.
  (reduction conf)꙳ (NPar (NEndpoint p s c) n) (NPar (NEndpoint p s' c') n') ∧
  (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd cSt0.ffi.ffi_state) ∧
  cpEval_valid conf p env0 s c n vs cvs cSt0 ∧
  letrec_network (NPar (NEndpoint p s c) n) ∧
  cSt0.ffi.ffi_state = (p,s.queues,n) ∧
  pletrec_vars_ok c ∧
  EVERY cletrec_vars_ok (MAP SND s.funs) ∧
  normalised s.queues
  ⇒
  ∃env cSt env' e' l' sst sst' vs'.
    stepr꙳
      (env0, smSt cSt0, Exp (compile_endpoint conf vs c), [])
      (env', sst, e', l') ∧
    stepr꙳
      (env, smSt cSt, Exp (compile_endpoint conf vs' c'), [])
      (env', sst', e', l') ∧
    ffi_eq conf (SND sst).ffi_state (SND sst').ffi_state ∧
    FST sst = FST sst' ∧
    (SND sst).oracle = (SND sst').oracle ∧
    (SND sst).io_events = (SND sst').io_events ∧
    cpEval_valid conf p env s' c' n' vs' cvs cSt ∧
    cSt.ffi.ffi_state = (p,s'.queues,n') ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p s' c') ⇒ ffi_has_node nd cSt.ffi.ffi_state)
Proof
  rpt strip_tac >>
  match_mp_tac network_NPar_forward_correctness_reduction_lemma >>
  simp[] >>
  irule_at Any ffi_eq_REFL >>
  gvs[] >>
  gvs[cpEval_valid_def,DISJ_IMP_THM,FORALL_AND_THM]
QED

Theorem network_forward_correctness_reduction:
  ∀conf s c n p s' c' n' cSt0 vs cvs env0.
    (reduction conf)꙳ n n' ∧
    REPN n ∧
    net_has_node n p ∧
    net_find p n  = SOME (NEndpoint p s  c ) ∧
    net_find p n' = SOME (NEndpoint p s' c') ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p s c) ⇒ ffi_has_node nd cSt0.ffi.ffi_state) ∧
    cpEval_valid conf p env0 s c (net_filter p n) vs cvs cSt0 ∧
    letrec_network (NPar (NEndpoint p s c) (net_filter p n)) ∧
    cSt0.ffi.ffi_state = (p,s.queues,net_filter p n) ∧
    pletrec_vars_ok c ∧
    EVERY cletrec_vars_ok (MAP SND s.funs) ∧
    normalised s.queues
  ⇒
  ∃env cSt env' e' l' sst sst' vs'.
    stepr꙳
      (env0, smSt cSt0, Exp (compile_endpoint conf vs c), [])
      (env', sst, e', l') ∧
    stepr꙳
      (env, smSt cSt, Exp (compile_endpoint conf vs' c'), [])
      (env', sst', e', l') ∧
    ffi_eq conf (SND sst).ffi_state (SND sst').ffi_state ∧
    FST sst = FST sst' ∧
    (SND sst).oracle = (SND sst').oracle ∧
    (SND sst).io_events = (SND sst').io_events ∧
    cpEval_valid conf p env s' c' (net_filter p n') vs' cvs cSt ∧
    cSt.ffi.ffi_state = (p,s'.queues,net_filter p n') ∧
    (∀nd. nd ∈ network_nodenames (NEndpoint p s' c') ⇒ ffi_has_node nd cSt.ffi.ffi_state)
Proof
  rpt strip_tac
  \\ irule network_NPar_forward_correctness_reduction
  \\ simp[] \\ qexists_tac ‘s’ \\ rw[] \\ gs[]
  >- (drule_then (qspec_then ‘p’ mp_tac) net_find_filter_reduction
      \\ impl_tac >- simp[net_has_node_IS_SOME_net_find]
      \\ simp[])
QED

val _ = export_theory ();
