open preamble
     endpoint_to_payloadTheory (* for compile_message only*)
     payloadLangTheory payload_to_cakemlTheory
     evaluateTheory terminationTheory ml_translatorTheory ml_progTheory evaluatePropsTheory
     semanticPrimitivesTheory
     ffiTheory
     comms_ffiTheory
     payloadPropsTheory
     payloadSemanticsTheory;

val _ = new_theory "payload_to_cakemlProof";

val pres_ref_def = Define
  ‘
  pres_ref cl =
     ∀v.
      ∃env exp mc dc refs' u.
        do_opapp [cl; v] = SOME (env,exp) ∧
        (∀sc :comms_state semanticPrimitives$state.
          (mc ≤ sc.clock ⇔ (evaluate sc env [exp] = (sc with <| clock := sc.clock - dc; refs := sc.refs ++ refs' |>, Rval [u]))) ∧
          (mc > sc.clock ⇔ ∃es. evaluate sc env [exp] = (es, Rerr (Rabort Rtimeout_error)))
        )
  ’;

val has_v_def = Define
  ‘has_v env n cfty f =
   (∃v. nsLookup env n = SOME v
        ∧ cfty f v
        ∧ pres_ref v)
  ’;

val WORD8 = “WORD:word8 -> v -> bool”;

val in_module_def = Define ‘
  in_module name =
  ∀x y (env:(modN,varN,v) namespace). nsLookup (nsBind x y env) name = nsLookup env name
  ’;

val env_asm_def = Define ‘
  env_asm env conf = (
    has_v env.v conf.concat (LIST_TYPE ^WORD8 --> LIST_TYPE ^WORD8 --> LIST_TYPE ^WORD8) $++ ∧ 
    has_v env.v conf.length (LIST_TYPE ^WORD8 --> NUM) LENGTH ∧
    has_v env.v conf.null (LIST_TYPE ^WORD8 --> BOOL) NULL ∧
    has_v env.v conf.take (LIST_TYPE ^WORD8 --> NUM --> LIST_TYPE ^WORD8) (combin$C TAKE) ∧
    has_v env.v conf.drop (LIST_TYPE ^WORD8 --> NUM --> LIST_TYPE ^WORD8) (combin$C DROP) ∧
    (∃v. nsLookup env.v conf.fromList = SOME v ∧
         (∀l lv.
           LIST_TYPE ^WORD8 l lv
           ⇒ ∀s1: unit semanticPrimitives$state. ∃env' exp ck1 ck2. do_opapp [v; lv] = SOME(env',exp)
               ∧ evaluate (s1 with clock := ck1) env' [exp] =
                  (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,Rval [Loc(LENGTH s1.refs)]))) ∧
    in_module conf.concat ∧
    in_module conf.length ∧
    in_module conf.null ∧
    in_module conf.take ∧
    in_module conf.drop ∧
    in_module conf.fromList)
  ’;


val evaluate_empty_state_norel = Q.prove(
  ‘∀s x refs refs' exp env ck1 ck2.
    evaluate (empty_state with <|clock := ck1; refs := refs|>) env [exp] =
             (empty_state with <|clock := ck2; refs := refs ++ refs'|>,Rval [x]) ⇒
    ∃ck1 ck2.
      evaluate (s with <|clock := ck1; refs := refs; ffi:= s.ffi|>) env [exp] =
      (s with <|clock := ck2; refs := refs ++ refs'; ffi:= s.ffi|>,Rval [x])’,
  rpt strip_tac >>
  qabbrev_tac ‘a1 = s with refs := refs’ >>
  ‘refs = a1.refs’ by(qunabbrev_tac ‘a1’ >> simp[]) >>
  fs[] >>
  drule (SIMP_RULE (srw_ss()) [ml_progTheory.eval_rel_def,PULL_EXISTS] evaluate_empty_state_IMP
         |> GEN_ALL) >>
  unabbrev_all_tac >>
  Cases_on ‘s’ >> fs[state_fn_updates]);

Theorem LUPDATE_REPLICATE
  ‘∀n m x y. n < m ⇒
   LUPDATE x n (REPLICATE m y) = REPLICATE n y ++ [x] ++ REPLICATE (m - (n + 1)) y’
 (Induct >> Cases >> rw[LUPDATE_def] >> simp[ADD1]);

Theorem padv_correct
 ‘∀env conf l lv le s1 s2 refs.
  env_asm env conf ∧
  LIST_TYPE ^WORD8 l lv ∧
  evaluate$evaluate s1 env [le] = (s2 with refs := s1.refs ++ refs, Rval [lv])
  ⇒
  ∃ck1 ck2 refs' num lv'.
  evaluate$evaluate (s1 with clock:= ck1) env [App Opapp [padv conf; le]] =
           (s2 with <|clock := ck2; refs := APPEND s1.refs refs'|>, Rval [Loc num]) ∧
  store_lookup num (APPEND s1.refs refs') = SOME(W8array(pad conf l))
  ’
 (rpt strip_tac >>
  drule evaluate_add_to_clock >>
  simp[] >>
  qabbrev_tac ‘ack = s2.clock’ >>
  fs[env_asm_def,in_module_def,has_v_def] >>
  strip_tac >>
  Q.REFINE_EXISTS_TAC ‘extra + s1.clock’ >>
  simp[Once evaluate_def] >>
  simp[padv_def,do_opapp_def,buffer_size_def,payload_size_def] >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[Once evaluate_def] >>
  simp[dec_clock_def,do_app_def,store_alloc_def,ml_progTheory.nsLookup_nsBind_compute,
       namespaceTheory.nsOptBind_def] >>
  ntac 6 (simp[Once evaluate_def]) >>
  simp[dec_clock_def,do_app_def,store_alloc_def,ml_progTheory.nsLookup_nsBind_compute,
       namespaceTheory.nsOptBind_def] >>
  ntac 6 (simp[Once evaluate_def]) >>
  simp[ml_progTheory.nsLookup_nsBind_compute] >>
  ntac 2 (simp[Once evaluate_def]) >>
  qpat_assum ‘(LIST_TYPE ^WORD8 --> NUM) LENGTH _’ (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
  simp[] >>
  disch_then drule >>
  qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
  disch_then(qspec_then ‘a1’ strip_assume_tac) >>
  qunabbrev_tac ‘a1’ >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
  Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack1)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack1’ >>
  drule evaluate_add_to_clock >>
  simp[SimpL “$==>”] >>
  disch_then(qspec_then ‘ack’ mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >>
  disch_then kall_tac >>
  fs[NUM_def,INT_def] >>  
  simp[do_app_def] >>
  simp[terminationTheory.do_eq_def,lit_same_type_def,Boolv_def,do_if_def] >>
  PURE_REWRITE_TAC [ADD_ASSOC] >>
  qpat_abbrev_tac ‘ack2 = ack + _’ >> pop_assum kall_tac >>
  Cases_on ‘LENGTH l = conf.payload_size’ >-
    (ntac 7 (simp[Once evaluate_def]) >>
     simp[do_app_def,store_lookup_def,EL_APPEND_EQN,store_assign_def,
          store_v_same_type_def,ml_progTheory.nsLookup_nsBind_compute,
          namespaceTheory.nsOptBind_def,lupdate_append2] >>
     ntac 10 (simp[Once evaluate_def]) >>
     qpat_assum ‘(LIST_TYPE WORD --> NUM --> LIST_TYPE WORD) (combin$C TAKE) _’ (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
     simp[] >> disch_then drule >>
     qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>     
     disch_then(qspec_then ‘a1’ strip_assume_tac) >>
     qunabbrev_tac ‘a1’ >> 
     Q.REFINE_EXISTS_TAC ‘extra + 1’ >> 
     simp[dec_clock_def] >>
     Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack3)’ >>
     Q.REFINE_EXISTS_TAC ‘extra + ack3’ >>
     drule evaluate_add_to_clock >>
     simp[SimpL “$==>”] >>
     disch_then(qspec_then ‘ack2’ mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     first_x_assum(qspecl_then [‘conf.payload_size’,‘Litv (IntLit (&conf.payload_size))’] mp_tac) >>
     impl_tac >- simp[NUM_def,INT_def] >>
     qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
     disch_then(qspec_then ‘a1’ strip_assume_tac) >>
     qunabbrev_tac ‘a1’ >>
     Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
     simp[dec_clock_def] >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack4 = ack2 + _’ >> pop_assum kall_tac >>
     Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack5)’ >>
     Q.REFINE_EXISTS_TAC ‘extra + ack5’ >>
     drule evaluate_add_to_clock >>
     simp[SimpL “$==>”] >>
     disch_then(qspec_then ‘ack4’ mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >>
     disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack6 = ack4 + _’ >> pop_assum kall_tac >>
     simp[Once evaluate_def] >>
     last_x_assum drule >>
     qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
     disch_then(qspec_then ‘empty_state with refs := a1’ mp_tac) >>
     simp[] >>
     qunabbrev_tac ‘a1’ >> strip_tac >>
     Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack7)’ >>
     Q.REFINE_EXISTS_TAC ‘extra + ack7’ >>
     drule evaluate_add_to_clock >>
     simp[SimpL “$==>”] >>
     disch_then(qspec_then ‘ack6’ mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack8 = ack6 + _’ >> pop_assum kall_tac >>
     simp[evaluate_def,namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute,
          do_app_def,store_lookup_def,EL_APPEND_EQN,copy_array_def,integerTheory.INT_ABS,
          LUPDATE_APPEND,LUPDATE_def] >>
     qmatch_goalsub_abbrev_tac ‘lhs < rhs’ >>
    ‘rhs = lhs’
     by (unabbrev_all_tac >>
         rw[] >- intLib.COOPER_TAC >>
         simp[GSYM (PURE_REWRITE_RULE [Once integerTheory.INT_ADD_SYM,integerTheory.INT_1]
                                      integerTheory.int_of_num)]) >>
     simp[] >>    
     MAP_EVERY qunabbrev_tac [‘lhs’,‘rhs’] >>
     simp[store_assign_def,store_v_same_type_def,EL_APPEND_EQN,
          semanticPrimitivesTheory.state_component_equality,LUPDATE_APPEND,
          LUPDATE_def] >>
     simp[TAKE_TAKE,pad_def] >>
     simp[DROP_LENGTH_TOO_LONG,LENGTH_LUPDATE] >>
     simp[REWRITE_RULE [ADD1] REPLICATE,LUPDATE_def] >>
     simp[TAKE_LENGTH_TOO_LONG]) >>
  rpt(qpat_x_assum ‘do_opapp _ = _’ kall_tac) >>
  ntac 8 (simp[Once evaluate_def]) >>
  qpat_assum ‘(LIST_TYPE ^WORD8 --> NUM) LENGTH _’ (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
  simp[] >> disch_then drule >>
  qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
  disch_then(qspec_then ‘a1’ strip_assume_tac) >>
  qunabbrev_tac ‘a1’ >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
  Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack3)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack3’ >>
  drule evaluate_add_to_clock >>
  simp[SimpL “$==>”] >>
  disch_then(qspec_then ‘ack2’ mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >>
  disch_then kall_tac >>
  fs[NUM_def,INT_def] >>  
  simp[do_app_def] >>
  simp[semanticPrimitivesTheory.opb_lookup_def,lit_same_type_def,Boolv_def,do_if_def] >>
  Cases_on ‘LENGTH l < conf.payload_size’ >-
    (simp[] >>
     ntac 7 (simp[Once evaluate_def]) >>
     simp[do_app_def,store_lookup_def,EL_APPEND_EQN,store_assign_def,
          store_v_same_type_def,ml_progTheory.nsLookup_nsBind_compute,
          namespaceTheory.nsOptBind_def,lupdate_append2] >>
     ntac 5 (simp[Once evaluate_def]) >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack4 = ack2 + _’ >> pop_assum kall_tac >>    
     last_x_assum drule >>
     qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
     disch_then(qspec_then ‘empty_state with refs := a1’ mp_tac) >>
     simp[] >>
     qunabbrev_tac ‘a1’ >> strip_tac >>
     Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack5)’ >>
     Q.REFINE_EXISTS_TAC ‘extra + ack5’ >>
     drule evaluate_add_to_clock >>
     simp[SimpL “$==>”] >>
     disch_then(qspec_then ‘ack4’ mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack6 = ack4 + _’ >> pop_assum kall_tac >>
     simp[evaluate_def,namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute,
          do_app_def,store_lookup_def,EL_APPEND_EQN,copy_array_def,integerTheory.INT_ABS,
          LUPDATE_APPEND,LUPDATE_def,opn_lookup_def] >>
     IF_CASES_TAC >- (
       spose_not_then kall_tac >>
       pop_assum mp_tac >>
       simp[integerTheory.INT_LT_SUB_RADD]) >>
     IF_CASES_TAC >- (
       spose_not_then kall_tac >>
       pop_assum mp_tac >>
       intLib.COOPER_TAC) >>
     simp[evaluate_def,namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute,
          do_app_def,store_lookup_def,EL_APPEND_EQN,copy_array_def,integerTheory.INT_ABS,
          LUPDATE_APPEND,LUPDATE_def,opn_lookup_def,store_assign_def,
          store_v_same_type_def] >>
     IF_CASES_TAC >- (
       spose_not_then kall_tac >>
       pop_assum mp_tac >>
       intLib.COOPER_TAC) >>
     simp[evaluate_def,namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute,
          do_app_def,store_lookup_def,EL_APPEND_EQN,copy_array_def,integerTheory.INT_ABS,
          LUPDATE_APPEND,LUPDATE_def,opn_lookup_def,store_assign_def,
          store_v_same_type_def,semanticPrimitivesTheory.state_component_equality] >>
     ‘Num (1 + (&conf.payload_size − &LENGTH l)) = 1 + (conf.payload_size - LENGTH l)’
       by(intLib.COOPER_TAC) >>
     ‘Num (&conf.payload_size − &LENGTH l) = conf.payload_size - LENGTH l’
       by(intLib.COOPER_TAC) >>
     simp[] >>
     simp[REWRITE_RULE [ADD1] REPLICATE,LUPDATE_APPEND,REWRITE_RULE [ADD1] LUPDATE_def] >>
     ‘conf.payload_size − LENGTH l = conf.payload_size − (LENGTH l + 1) + 1’
       by(intLib.COOPER_TAC) >>
     pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
     PURE_REWRITE_TAC[REWRITE_RULE [ADD1] LUPDATE_def] >>
     simp[TAKE_cons] >>     
     IF_CASES_TAC >- (
        spose_not_then kall_tac >>
        pop_assum mp_tac >> intLib.COOPER_TAC) >>
     ‘Num (1 + (&conf.payload_size − &LENGTH l) + &LENGTH l) = conf.payload_size + 1’
       by(intLib.COOPER_TAC) >>
     simp[DROP_LENGTH_TOO_LONG,LENGTH_LUPDATE,LENGTH_REPLICATE] >>
     simp[LUPDATE_REPLICATE,TAKE_APPEND] >>
     simp[TAKE_LENGTH_TOO_LONG,LENGTH_REPLICATE] >>
     simp[pad_def]) >>
    (simp[] >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack4 = ack2 + _’ >> pop_assum kall_tac >>
     ntac 7 (simp[Once evaluate_def]) >>
     simp[do_app_def,store_lookup_def,EL_APPEND_EQN,store_assign_def,
          store_v_same_type_def,ml_progTheory.nsLookup_nsBind_compute,
          namespaceTheory.nsOptBind_def,lupdate_append2] >>
     ntac 10 (simp[Once evaluate_def]) >>
     qpat_assum ‘(LIST_TYPE WORD --> NUM --> LIST_TYPE WORD) (combin$C TAKE) _’ (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
     simp[] >> disch_then drule >>
     qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>     
     disch_then(qspec_then ‘a1’ strip_assume_tac) >>
     qunabbrev_tac ‘a1’ >>
     Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack5)’ >>
     Q.REFINE_EXISTS_TAC ‘extra + ack5’ >>
     drule evaluate_add_to_clock >>
     simp[SimpL “$==>”] >>
     disch_then(qspec_then ‘ack4’ mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     first_x_assum(qspecl_then [‘conf.payload_size’,‘Litv (IntLit (&conf.payload_size))’] mp_tac) >>
     impl_tac >- simp[NUM_def,INT_def] >>
     qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
     disch_then(qspec_then ‘a1’ strip_assume_tac) >>
     qunabbrev_tac ‘a1’ >>
     Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
     simp[dec_clock_def] >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack6 = ack4 + _’ >> pop_assum kall_tac >>
     Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack7)’ >>
     Q.REFINE_EXISTS_TAC ‘extra + ack7’ >>
     drule evaluate_add_to_clock >>
     simp[SimpL “$==>”] >>
     disch_then(qspec_then ‘ack6’ mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >>
     disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack8 = ack6 + _’ >> pop_assum kall_tac >>
     simp[Once evaluate_def] >>
     last_x_assum drule >>
     qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
     disch_then(qspec_then ‘empty_state with refs := a1’ mp_tac) >>
     simp[] >>
     qunabbrev_tac ‘a1’ >> strip_tac >>
     Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN ‘s2 with refs := s1.refs ++ refs’ dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack9)’ >>
     Q.REFINE_EXISTS_TAC ‘extra + ack9’ >>
     drule evaluate_add_to_clock >>
     simp[SimpL “$==>”] >>
     disch_then(qspec_then ‘ack8’ mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac ‘ack10 = ack8 + _’ >> pop_assum kall_tac >>
     simp[evaluate_def,namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute,
          do_app_def,store_lookup_def,EL_APPEND_EQN,copy_array_def,integerTheory.INT_ABS,
          LUPDATE_APPEND,LUPDATE_def] >>
     IF_CASES_TAC >-
       (spose_not_then kall_tac >> pop_assum mp_tac >> intLib.COOPER_TAC) >>
     simp[store_assign_def,store_v_same_type_def,EL_APPEND_EQN,
          semanticPrimitivesTheory.state_component_equality,LUPDATE_APPEND,
          REWRITE_RULE [ADD1] REPLICATE,LUPDATE_def,TAKE_TAKE] >>
     rw[pad_def,DROP_NIL] >> intLib.COOPER_TAC)
  );

val ffi_accepts_rel_def = Define ‘
  ffi_accepts_rel stpred pred oracle =
  ∀st s conf bytes.
    stpred st.ffi_state ∧ st.oracle = oracle ∧ pred s conf bytes ⇒
    ∃ffi. st.oracle s st.ffi_state conf bytes = Oracle_return ffi bytes ∧
          stpred ffi’;

val send_events_def = Define ‘
  send_events conf dest d =
  MAP (λm. IO_event "send" dest (ZIP (m,m)))(compile_message conf d)’;

val update_state_def = Define ‘
  (update_state st oracle [] = st) ∧
  (update_state st oracle (IO_event s c b::es) =
   update_state (@st'. oracle s st c (MAP FST b) = Oracle_return st' (MAP SND b))
                oracle es)’;

val LUPDATE_SAME' = Q.prove(
  ‘n < LENGTH ls ∧ EL n ls = a ⇒ LUPDATE a n ls = ls’,
  metis_tac[LUPDATE_SAME]);

Theorem sendloop_correct
 ‘∀conf l env env' lv le s refs stpred dest.
  env_asm env' conf ∧
  conf.payload_size ≠ 0 ∧
  LIST_TYPE ^WORD8 l lv ∧
  nsLookup env.v (Short "sendloop") = SOME(Recclosure env' (sendloop conf (MAP (CHR o w2n) dest)) "sendloop") ∧
  nsLookup env.v (Short "x") = SOME lv ∧
  stpred s.ffi.ffi_state ∧
  ffi_accepts_rel
    stpred
    (λs c bytes. s = "send" ∧ c = dest ∧ LENGTH bytes = SUC conf.payload_size)
    s.ffi.oracle
  ⇒
  ∃ck1 ck2 refs' num lv'.
  evaluate$evaluate (s with clock:= ck1) env [App Opapp [Var (Short "sendloop"); Var(Short "x")]] =
                    (s with
                       <|clock := ck2; refs := APPEND s.refs refs';
                         ffi:= s.ffi with
                         <|io_events := s.ffi.io_events ++ send_events conf dest l;
                           ffi_state := update_state s.ffi.ffi_state s.ffi.oracle (send_events conf dest l)
                          |>
                        |>, Rval [Conv NONE []])’
 (ho_match_mp_tac compile_message_ind>>
  rpt strip_tac >>
  ntac 4 (simp[Once evaluate_def]) >>
  simp[do_opapp_def] >>
  ntac 2 (simp[Once sendloop_def]) >>
  simp[find_recfun_def] >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
  simp[Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ env1’ >>
  ‘env_asm env1 conf’
    by fs[Abbr ‘env1’,env_asm_def,build_rec_env_def,sendloop_def,has_v_def,in_module_def] >>
  drule(INST_TYPE [alpha |-> beta] padv_correct) >> disch_then drule >>
  disch_then(qspecl_then [‘Var(Short "x")’,‘s’,‘s’,‘[]’] mp_tac) >>
  impl_tac >- simp[evaluate_def,Abbr ‘env1’,semanticPrimitivesTheory.state_component_equality] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack1)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack1’ >>
  dxrule evaluate_add_to_clock >>
  simp[] >> disch_then kall_tac >>
  ntac 4 (simp[Once evaluate_def]) >>  
  simp[ml_progTheory.nsLookup_nsBind_compute,namespaceTheory.nsOptBind_def,
       do_app_def,ffiTheory.call_FFI_def] >>
  simp[Once evaluate_def] >>
  qhdtm_assum ‘ffi_accepts_rel’ (mp_tac o REWRITE_RULE [ffi_accepts_rel_def]) >>
  disch_then drule >> simp[] >>
  disch_then(qspec_then ‘pad conf l’ mp_tac) >>
  impl_keep_tac >- rw[pad_def] >>
  strip_tac >>
  simp[IMPLODE_EXPLODE_I,MAP_MAP_o,o_DEF,
       SIMP_RULE std_ss [o_DEF] n2w_ORD_CHR_w2n] >>
  fs[store_assign_def,store_lookup_def,store_v_same_type_def,
     LUPDATE_SAME'] >>
  simp[payload_size_def] >>
  ntac 8 (simp[Once evaluate_def]) >>
  simp[do_app_def,ml_progTheory.nsLookup_nsBind_compute,
       namespaceTheory.nsOptBind_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ env2’ >>
  ‘env_asm env2 conf’
    by fs[Abbr ‘env2’,env_asm_def,build_rec_env_def,sendloop_def,has_v_def,in_module_def] >>
  first_assum (strip_assume_tac o REWRITE_RULE[env_asm_def]) >>
  qunabbrev_tac ‘env2’ >>
  fs[has_v_def] >>
  qpat_assum ‘(LIST_TYPE ^WORD8 --> NUM) LENGTH _’ (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
  simp[] >> disch_then drule >>
  qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
  disch_then(qspec_then ‘a1’ strip_assume_tac) >>
  qunabbrev_tac ‘a1’ >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
    qmatch_goalsub_abbrev_tac ‘ffi_fupd (K a1)’ >>
  Q.ISPEC_THEN ‘s with ffi := a1’ dxrule evaluate_empty_state_norel >>
  qunabbrev_tac ‘a1’ >>
  strip_tac >>
  rename1 ‘ack2 + _’ >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack3)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack3’ >>
  dxrule evaluate_add_to_clock >>
  simp[SimpL “$==>”] >>
  disch_then(qspec_then ‘ack2’ mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >>
  disch_then kall_tac >>
  fs[NUM_def,INT_def] >>
  PURE_REWRITE_TAC [ADD_ASSOC] >>
  qpat_abbrev_tac ‘ack4 = ack2 + _’ >> pop_assum kall_tac >>
  simp[do_if_def,opb_lookup_def] >>
  IF_CASES_TAC >- (* base case of induction: LENGTH l <= conf.payload_size *)
    (simp[Once evaluate_def,do_con_check_def,build_conv_def,semanticPrimitivesTheory.state_component_equality,ffiTheory.ffi_state_component_equality] >>
     fs[pad_def] >> every_case_tac >>
     simp[send_events_def,Once compile_message_def,final_def,pad_def,update_state_def] >>
     simp[Once compile_message_def,pad_def,final_def]) >>
  (* Inductive case: L *)
  simp[] >>
  ntac 8 (simp[Once evaluate_def]) >>
  qpat_assum ‘(LIST_TYPE WORD --> NUM --> LIST_TYPE WORD) (combin$C DROP) _’ (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
  simp[] >> disch_then drule >>
  qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>     
  disch_then(qspec_then ‘a1’ strip_assume_tac) >>
  qunabbrev_tac ‘a1’ >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
  qmatch_goalsub_abbrev_tac ‘ffi_fupd (K a1)’ >>
  Q.ISPEC_THEN ‘s with ffi := a1’ dxrule evaluate_empty_state_norel >>
  qunabbrev_tac ‘a1’ >>
  strip_tac >>  
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack5)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack5’ >>
  dxrule evaluate_add_to_clock >>
  simp[SimpL “$==>”] >>
  disch_then(qspec_then ‘ack4’ mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >> disch_then kall_tac >>
  first_x_assum(qspecl_then [‘conf.payload_size’,‘Litv (IntLit (&conf.payload_size))’] mp_tac) >>
  impl_tac >- simp[NUM_def,INT_def] >>
  qmatch_goalsub_abbrev_tac ‘refs_fupd (K a1)’ >>
  disch_then(qspec_then ‘a1’ strip_assume_tac) >>
  qunabbrev_tac ‘a1’ >>
  qmatch_goalsub_abbrev_tac ‘ffi_fupd (K a1)’ >>
  Q.ISPEC_THEN ‘s with ffi := a1’ dxrule evaluate_empty_state_norel >>
  qunabbrev_tac ‘a1’ >>
  strip_tac >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
  PURE_REWRITE_TAC [ADD_ASSOC] >>
  qpat_abbrev_tac ‘ack6 = ack4 + _’ >> pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack7)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack7’ >>
  dxrule evaluate_add_to_clock >>
  simp[SimpL “$==>”] >>
  disch_then(qspec_then ‘ack6’ mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >>
  disch_then kall_tac >>
  PURE_REWRITE_TAC [ADD_ASSOC] >>
  qpat_abbrev_tac ‘ack8 = ack6 + _’ >> pop_assum kall_tac >>
  fs[send_events_def,final_pad_LENGTH] >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ env2’ >>  
  qpat_x_assum ‘env_asm env' conf’ assume_tac >>
  last_x_assum drule >> disch_then drule >>
  disch_then(qspec_then ‘env2’ mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘ffi_fupd (K a1)’ >>
  qmatch_goalsub_abbrev_tac ‘refs_fupd (K a2)’ >>
  disch_then(qspec_then ‘s with <|ffi := a1; refs := a2 |>’ mp_tac) >>
  disch_then(qspecl_then [‘stpred’,‘dest’] mp_tac) >>
  qunabbrev_tac ‘a1’ >> qunabbrev_tac ‘a2’ >>
  impl_tac >-
    (unabbrev_all_tac >>
     simp[sendloop_def,build_rec_env_def,o_DEF,namespaceTheory.nsOptBind_def]) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack9)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack9’ >>
  dxrule evaluate_add_to_clock >>
  simp[SimpL “$==>”] >>
  disch_then(qspec_then ‘ack8’ mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >> disch_then kall_tac >>
  simp[semanticPrimitivesTheory.state_component_equality,ffiTheory.ffi_state_component_equality] >>
  conj_tac >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [compile_message_def])) >>
  simp[final_pad_LENGTH,update_state_def]
  );

val DATUM = “LIST_TYPE ^WORD8”;

(* ASSUMPTIONS ABOUT CURRENTLY UNIMPLEMENTED COMPILER FEATURES *)

(* enc_ok (v sem_env) -> string list -> LIST_TYPE (LIST_TYPE DATUM -> DATUM) -> Boolv_def *)

val enc_ok_def =
    Define
    ‘
    (enc_ok _ _ [] [] = T) ∧
    (enc_ok conf ckEnv (f::fs) (n::ns) =
       ((∃cl.
            (SOME cl = nsLookup (ckEnv.v) (getLetID conf n)) ∧
            (LIST_TYPE ^(DATUM) --> ^DATUM) f cl
         ) ∧
        enc_ok conf ckEnv fs ns
        )
    ) ∧
    (enc_ok _ _ _ _ = F)
    ’;

(* UNDERSTANDING WHAT VARIABLES AND CONFIG MEAN IN CAKEML LAND - CONSISTENCY OF SEMANTIC ENVIRONMENT *)

(* Check the semantic environment contains all the variable bindings in
   the payload state and also matches all the config assumptions        *)

val sem_env_cor_def =
    Define
    ‘
    sem_env_cor conf pySt ckEnv =
       ((∀ n v. (FLOOKUP pySt.bindings n = SOME v)
                 ⇒ (∃v'. (nsLookup (ckEnv.v) (Short n) = SOME v') ∧
                         ^(DATUM) v v')
         ) ∧
        env_asm ckEnv conf
        )
    ’;

(* UNDERSTANDING WHAT LABELS MEAN IN CAKEML LAND - CONSISTENCY OF STATE *)

(* CHECK OF FFI STATE AND PAYLOAD STATE CONSISTENCY WITH LABELS *)
val check_ffi_past_def =
    Define
    ‘
    check_ffi_past pySt ffiSt = (LTAKE (LENGTH pySt.queue) ffiSt.receive_messages = SOME pySt.queue)
    ’;

val get_ffi_future_def =
    Define
    ‘
    get_ffi_future pySt ffiSt = case (LDROP (LENGTH pySt.queue) ffiSt.receive_messages) of
                                        SOME x => x
                                    |   NONE   => LNIL
    ’;

val ffi_stat_prog_cons_def =
    Define
    ‘
    ffi_stat_prog_cons pySt1 ffiSt1 lab pySt2 ffiSt2 =
        ((check_ffi_past pySt1 ffiSt1) ∧
        (check_ffi_past pySt2 ffiSt2) ∧
        (case lab of
                LReceive src data _ => (get_ffi_future pySt1 ffiSt1 = (src,data):::get_ffi_future pySt2 ffiSt2)
            |   _                   => (get_ffi_future pySt1 ffiSt1 = get_ffi_future pySt2 ffiSt2)
        ) ∧
        (case lab of
                LSend _ data dest   => (ffiSt2.sent_messages = (dest,data)::ffiSt1.sent_messages)
            |   _                   => (ffiSt2.sent_messages = ffiSt1.sent_messages)
        )
        )
    ’;

val stat_prog_cor_def =
    Define
    ‘
    stat_prog_cor pySt1 ckSt1 lab pySt2 ckSt2 =
        (ffi_stat_prog_cons pySt1 (ckSt1.ffi.ffi_state) lab pySt2 (ckSt2.ffi.ffi_state) ∧
        (ckSt1.ffi.oracle = comms_ffi_oracle) ∧
        (ckSt2.ffi.oracle = comms_ffi_oracle))
    ’;

Theorem payload_cakeml_proj_irrelrefs:
  ∀sc0 se conf vs ep sc1 res.
    env_asm se conf ∧
    evaluate sc0  se  [compile_endpoint conf vs ep]  = (sc1, res)
    ⇒
    ∃δ. sc1.refs = sc0.refs ++ δ ∧
        ∀refs'. evaluate (sc0 with refs := refs') se [compile_endpoint conf vs  ep] =
                (sc1 with refs := refs' ++ δ, res)
Proof
  Induct_on ‘ep’
  (* Nil endpoint case *)
  >- (rw[compile_endpoint_def,evaluate_def] >>
      fs[build_conv_def,do_con_check_def])
  (* Send endpoint case *)
  >- (simp[compile_endpoint_def,evaluate_def] >>
      rw[AllCaseEqs ()] >>
      fs[PULL_EXISTS] >>
      rename [‘evaluate _ lenv [lexp] = (_,_)’,
                  ‘nsLookup _ (Short mlistNm) = SOME mval’,
                  ‘nsLookup _ conf.length = SOME lc’]
      >- (drule_then assume_tac (CONJUNCT1 evaluate_length) >>
          fs[] >>
          rename [‘evaluate _ lenv [lexp] = (_,Rval lvs)’] >>
          ‘∃lv. lvs = [lv]’
            by (Cases_on ‘lvs’ >> fs[]) >>
          rw[] >> fs[] >>
          ‘pres_ref lc’
            by fs[env_asm_def,has_v_def] >>
          fs[pres_ref_def] >>
          cheat
          (*
          pop_assum (qspec_then ‘mval’ (qx_choose_then ‘δ’ assume_tac)) >>
          qexists_tac ‘δ’ >>
          rfs[] >>
          fs[eval_rel_def] >>
          cheat
          *)
          )
      >- (cheat)
      >- (cheat)
      >- (cheat)
      >- (cheat))
(*          >> 
        )
      Cases_on ‘nsLookup se.v (Short s)’ >>
      fs[] >>
      Cases_on ‘nsLookup se.v conf.length’ >>
      fs[] >>
      Cases_on ‘res’ >>
      fs[] >>
      qexists_tac ‘refs'’ >>
      simp[] >>
      Cases_on ‘do_opapp [x'; x]’
      >- fs[]
      >- (fs[]


      >- (fs[] >>
          Cases_on ‘res’ >>
          fs[] >>
          qexists_tac ‘refs'’ >>
          simp[])
      >- (fs[] >>
          Cases_on ‘nsLookup se.v conf.length’ >>
          fs[] >>)


      fs[]
      Cases_on ‘’ *)
  >- (cheat)
  >- (cheat)
  >- (cheat)
QED


Theorem payload_cakeml_proj_correct:
    ∀conf p sp sp' ep ep' L.
        trans conf (NEndpoint p sp ep) L (NEndpoint p sp' ep')
        ⇒  (∀se vs se' vs' sc sc'.
                (enc_ok conf se  (letfuns ep)  vs)  ∧
                (enc_ok conf se' (letfuns ep') vs') ∧
                (sem_env_cor conf sp  se)  ∧
                (sem_env_cor conf sp' se') ∧
                (stat_prog_cor sp sc L sp' sc')
                ⇒ ∃mc s s' res.
                    (evaluate (sc  with clock := mc)  se  [compile_endpoint conf vs  ep]  = (s, res)) ∧
                    (evaluate (sc' with clock := mc)  se' [compile_endpoint conf vs' ep'] = (s',res)) ∧
                    (s.ffi.ffi_state = s'.ffi.ffi_state) 
            )
Proof
    Cases_on ‘ep’
    (* Nil Endpoint Case *)
    >- (rpt strip_tac >>
        Cases_on ‘L’ >>
        fs[Once trans_cases] >>
        (* Only LReceive Possible *)
        rw[compile_endpoint_def,evaluate_def] >>
        rw[do_con_check_def,build_conv_def] >>
        (* We don't actually need all the assumptions *)
        fs[stat_prog_cor_def,ffi_stat_prog_cons_def] >>
        (* Everything else is equal in the record by assumptions *)
        ‘sc.ffi.ffi_state.receive_messages = sc'.ffi.ffi_state.receive_messages’
            suffices_by rw[comms_state_component_equality] >>
        (* Essentially split the lists and abbreviate to allow for proof *)
        rw[LNTH_EQ] >>
        fs[check_ffi_past_def] >>
        qabbrev_tac ‘LQ = LENGTH sp.queue’ >>
        qabbrev_tac ‘OR = sc.ffi.ffi_state.receive_messages’ >>
        qabbrev_tac ‘NR = sc'.ffi.ffi_state.receive_messages’ >>
        ‘OR = LAPPEND (fromList (THE (LTAKE LQ OR))) (THE (LDROP LQ OR))’
            by (‘¬LFINITE OR ∨ LQ ≤ (THE (LLENGTH OR))’
                    by (CCONTR_TAC >>
                        Cases_on ‘LLENGTH OR’ >>
                        fs[LTAKE_LLENGTH_NONE] >>
                        fs[LLENGTH]) >>
                metis_tac[LTAKE_DROP]) >>
        ‘NR = LAPPEND (fromList (THE (LTAKE LQ NR))) (THE (LDROP LQ NR))’
            by (‘¬LFINITE NR ∨ LQ ≤ (THE (LLENGTH NR))’
                    by (CCONTR_TAC >>
                        Cases_on ‘LLENGTH NR’ >>
                        fs[LTAKE_LLENGTH_NONE] >>
                        fs[LLENGTH]) >>
                metis_tac[LTAKE_DROP]) >>
        first_x_assum (SUBST1_TAC) >>
        first_x_assum (SUBST1_TAC) >>
        (* Can quickly reduce to the tail equality *)
        ‘LTAKE LQ NR = SOME sp.queue’
            by (CCONTR_TAC >>
                Cases_on ‘LTAKE LQ NR’ >>
                Cases_on ‘LNTH LQ NR’ >>
                fs[LTAKE_SNOC_LNTH]) >>
        rw[LNTH_LAPPEND] >>
        ‘LDROP LQ OR = LDROP LQ NR’
            suffices_by rw[] >>
        (* We can now squeeze out an assumption to get the info we need *)
        fs[get_ffi_future_def] >>
        Cases_on ‘LDROP LQ OR’ >>
        fs[] >>
        Cases_on ‘LDROP (SUC LQ) NR’
        >- (fs[LDROP_SUC]
            >- (‘LFINITE NR’
                    by metis_tac[LDROP_NONE_LFINITE] >>
                (* We can prove this case nonsensical based on the known info on LTAKE (SUC LQ) NR *)
                ‘LQ = THE (LLENGTH NR)’
                    suffices_by (rpt strip_tac >>
                                ‘∃y. LDROP LQ NR = SOME y’
                                    by rw[LFINITE_DROP] >>
                                fs[]) >>
                ‘THE (LLENGTH NR) ≤ LQ’
                    by (CCONTR_TAC >>
                        ‘∃y. LDROP LQ NR = SOME y’
                            by rw[LFINITE_DROP] >>
                        fs[]) >>
                ‘LQ ≤ THE (LLENGTH NR)’
                    by (CCONTR_TAC >>
                        ‘∃l. LLENGTH NR = SOME l’
                            by fs[LFINITE_LLENGTH] >>
                        ‘l' < SUC LQ’
                            by fs[THE_DEF] >>
                        ‘LTAKE (SUC LQ) NR = NONE’
                            by metis_tac[LTAKE_LLENGTH_NONE] >>
                        fs[]) >>
                simp[])
            >- (‘LLENGTH NR = SOME LQ’
                    by metis_tac[LDROP_EQ_LNIL] >>
                ‘LQ < SUC LQ’
                    by rw[] >>
                ‘LTAKE (SUC LQ) NR = NONE’
                    by metis_tac[LTAKE_LLENGTH_NONE] >>
                fs[])
            )
        >- (fs[LDROP_SUC] >>
            Cases_on ‘x''’
            >> fs[LTL]
            >> ‘SOME h = LNTH LQ NR’
                    by rw[LNTH_HD_LDROP]
            >> ‘LNTH LQ NR = SOME (EL LQ (SNOC (l,l0) sp.queue))’
                    by (‘LQ < SUC LQ’
                            by rw[] >>
                        metis_tac[LTAKE_LNTH_EL])
            >> ‘(l,l0) = EL LQ (SNOC (l,l0) sp.queue)’
                    suffices_by fs[]
            >> qunabbrev_tac ‘LQ’
            >> rw[EL_LENGTH_SNOC])
        )
    (* The Send endpoint case *)
    >- (Cases_on ‘L’ >>
        simp[Once trans_cases]
        (* Send Label Case *)
        >- (rw[compile_endpoint_def]
            (* Final Message Case *)
            >- ((* This is just essentially translating CakeML AST back into HOL! *)
                fs[sem_env_cor_def] >>
                ‘∃ dc. nsLookup se.v (Short s) = SOME dc ∧ LIST_TYPE WORD d dc’
                    by metis_tac[] >>
                ‘has_v se.v conf.length (LIST_TYPE ^WORD8 --> NUM) LENGTH’
                    by metis_tac[env_asm_def] >>
                fs[has_v_def] >>
                rename [‘(_ --> _) LENGTH lengthc’] >>
                fs[Arrow_def, AppReturns_def] >>
                cheat)
                (*
                pop_assum (drule_then assume_tac) >>
                rw[evaluate_def] >>
                ‘∃env exp. do_opapp [lengthc;dc] = SOME (env,exp)’
                    by metis_tac[] >>
                ‘∃u. NUM (LENGTH d) u’
                    by metis_tac[] >>
                ‘∀st :comms_state semanticPrimitives$state.
                    ∃refs'. eval_rel st env exp (st with refs := st.refs ++ refs') u’
                    by (‘∀refs.
                             ∃refs'.
                                 eval_rel (empty_state with refs := refs) env exp
                                   (empty_state with refs := refs ++ refs') u’
                            by (‘∀ a u1 u2. NUM a u1 ∧ NUM a u2 ⇒ (u1 = u2)’
                                    by rw[NUM_def,INT_def] >>
                                rpt strip_tac >>
                                first_x_assum (qspec_then ‘refs’ assume_tac) >>
                                fs[] >>
                                ‘SOME (env,exp) = SOME (env',exp')’
                                    by metis_tac[EQ_SYM_EQ] >>
                                ‘env = env'’
                                    by rw[] >>
                                ‘exp = exp'’
                                    by rw[] >>
                                rw[] >>
                                metis_tac[]) >>
                        strip_tac >>
                        pop_assum (qspec_then ‘st.refs’ assume_tac) >>
                        fs[] >>
                        qexists_tac ‘refs'’ >>
                        irule evaluate_empty_state_IMP >>
                        simp[]) >>
                qpat_x_assum ‘∀r. ∃a b c d. P’ kall_tac >>
                simp[] >>
                Q.REFINE_EXISTS_TAC ‘SUC mc’ >>
                simp[] >>
                simp[dec_clock_def] >>
                fs[eval_rel_def] >>
                pop_assum (qspec_then ‘sc’ strip_assume_tac) >>
                Q.REFINE_EXISTS_TAC ‘mc + ck1’ >>
                ‘∀mc.
                  (evaluate (sc with clock := mc + ck1) env [exp] =
                    (sc with <|clock := mc + ck2; refs := sc.refs ++ refs'|>, Rval [u]))’
                  by (strip_tac >>
                      qabbrev_tac ‘es = (sc with clock := ck1)’ >>
                      qabbrev_tac ‘es' = sc with <|clock := ck2; refs := sc.refs ++ refs'|>’ >>
                      ‘evaluate (es with clock := es.clock + mc) env [exp]
                        = (es' with clock := es'.clock + mc,Rval [u])’
                        suffices_by  rw[Abbr ‘es’, Abbr ‘es'’] >>
                      ‘evaluate es env [exp] = (es', Rval [u])’
                        suffices_by rw[evaluate_add_to_clock] >>
                      simp[]) >>
                rw[] >>
                simp[do_app_def] >>
                fs[NUM_def,INT_def] >>
                rw[opb_lookup_def] >>
                rw[do_if_def]
                *)
                (* Case where LENGTH d <= n *)
                (*
                >- (fs[letfuns_def] >>
                *)
                    (* Need ref independence *)
                    (* Need constancy of compile semantics under relation of vs to vs' *)
                (*
                    cheat)
                *)
            (* Intermediate Message Case *)
            >- (cheat)
          )     
        (* Receive Label Case *)
        >- (cheat)
      )
    >- (cheat)
    >- (cheat)
    >- (cheat)
QED

val _ = export_theory ();