open preamble
     endpoint_to_payloadTheory (* for compile_message only*)
     payloadLangTheory payload_to_cakemlTheory
     evaluateTheory terminationTheory ml_translatorTheory ml_progTheory evaluatePropsTheory
     namespaceTheory
     semanticPrimitivesTheory
     ffiTheory
     comms_ffiTheory
     payloadPropsTheory
     payloadSemanticsTheory;

val _ = new_theory "payload_to_cakemlProof";


Definition has_v_def:
  has_v env n cfty f =
   (∃v. nsLookup env n = SOME v
        ∧ cfty f v)
End

val WORD8 = “WORD:word8 -> v -> bool”;

Definition in_module_def:
  in_module name =
  ∀x y (env:(modN,varN,v) namespace). nsLookup (nsBind x y env) name = nsLookup env name
End

Definition env_asm_def:
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
End


Theorem evaluate_empty_state_norel:
  ∀s x refs refs' exp env ck1 ck2.
    evaluate (empty_state with <|clock := ck1; refs := refs|>) env [exp] =
             (empty_state with <|clock := ck2; refs := refs ++ refs'|>,Rval [x]) ⇒
    ∃ck1 ck2.
      evaluate (s with <|clock := ck1; refs := refs; ffi:= s.ffi|>) env [exp] =
      (s with <|clock := ck2; refs := refs ++ refs'; ffi:= s.ffi|>,Rval [x])
Proof
  rpt strip_tac >>
  qabbrev_tac ‘a1 = s with refs := refs’ >>
  ‘refs = a1.refs’ by(qunabbrev_tac ‘a1’ >> simp[]) >>
  fs[] >>
  drule (SIMP_RULE (srw_ss()) [ml_progTheory.eval_rel_def,PULL_EXISTS] evaluate_empty_state_IMP
         |> GEN_ALL) >>
  unabbrev_all_tac >>
  Cases_on ‘s’ >> fs[state_fn_updates]
QED

Theorem LUPDATE_REPLICATE:
  ∀n m x y. n < m ⇒
   LUPDATE x n (REPLICATE m y) = REPLICATE n y ++ [x] ++ REPLICATE (m - (n + 1)) y
Proof
  Induct >> Cases >> rw[LUPDATE_def] >> simp[ADD1]
QED

Theorem padv_correct:
 ∀env conf l lv le s1 s2 refs.
  env_asm env conf ∧
  LIST_TYPE ^WORD8 l lv ∧
  evaluate$evaluate s1 env [le] = (s2 with refs := s1.refs ++ refs, Rval [lv])
  ⇒
  ∃ck1 ck2 refs' num lv'.
  evaluate$evaluate (s1 with clock:= ck1) env [App Opapp [padv conf; le]] =
           (s2 with <|clock := ck2; refs := APPEND s1.refs refs'|>, Rval [Loc num]) ∧
  store_lookup num (APPEND s1.refs refs') = SOME(W8array(pad conf l))
Proof
  rpt strip_tac >>
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
QED

Definition ffi_accepts_rel_def:
  ffi_accepts_rel stpred pred oracle =
  ∀st s conf bytes.
    stpred st.ffi_state ∧ st.oracle = oracle ∧ pred s conf bytes ⇒
    ∃ffi. st.oracle s st.ffi_state conf bytes = Oracle_return ffi bytes ∧
          stpred ffi
End

Definition send_events_def:
  send_events conf dest d =
  MAP (λm. IO_event "send" dest (ZIP (m,m)))(compile_message conf d)
End

Definition update_state_def:
  (update_state st oracle [] = st) ∧
  (update_state st oracle (IO_event s c b::es) =
   update_state (@st'. oracle s st c (MAP FST b) = Oracle_return st' (MAP SND b))
                oracle es)
End

Theorem LUPDATE_SAME':
  n < LENGTH ls ∧ EL n ls = a ⇒ LUPDATE a n ls = ls
Proof
  metis_tac[LUPDATE_SAME]
QED

Theorem sendloop_correct:
  ∀conf l env env' lv le s refs stpred dest.
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
                        |>, Rval [Conv NONE []])
Proof
  ho_match_mp_tac compile_message_ind>>
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
QED

val DATUM = “LIST_TYPE ^WORD8”;

(* ASSUMPTIONS ABOUT CURRENTLY UNIMPLEMENTED COMPILER FEATURES *)

(* enc_ok (v sem_env) -> string list -> LIST_TYPE (LIST_TYPE DATUM -> DATUM) -> Boolv_def *)

Definition enc_ok_def:
    (enc_ok _ _ [] [] = T) ∧
    (enc_ok conf cEnv (f::fs) (n::ns) =
       ((∃cl.
            (SOME cl = nsLookup (cEnv.v) (getLetID conf n)) ∧
            (LIST_TYPE ^(DATUM) --> ^DATUM) f cl
         ) ∧
        enc_ok conf cEnv fs ns
        )
    ) ∧
    (enc_ok _ _ _ _ = F)
End

(* UNDERSTANDING WHAT VARIABLES AND CONFIG MEAN IN CAKEML LAND - CONSISTENCY OF SEMANTIC ENVIRONMENT *)

(* Check the payload code and state make sense wrt. free variables *)
Definition pFv_def[simp]:
  pFv Nil = {} ∧
  pFv (Send _ fv _ npCd) = fv INSERT pFv npCd ∧
  pFv (Receive _ fv _ npCd) = fv INSERT pFv npCd ∧
  pFv (IfThen fv npCd1 npCd2) = fv INSERT pFv npCd1 ∪ pFv npCd2 ∧
  pFv (Let bv _ fvs npCd) = (pFv npCd DELETE bv) ∪ set fvs
End

Definition pSt_pCd_corr_def:
  pSt_pCd_corr pSt pCd ⇔ ∀vn. vn ∈ pFv pCd
                              ⇒ ∃vv. FLOOKUP pSt.bindings vn = SOME vv
End

(* Check the semantic environment contains all the variable bindings in
   the payload state and also matches all the config assumptions        *)

Definition sem_env_cor_def:
    sem_env_cor conf pSt cEnv ⇔
        env_asm cEnv conf ∧
        ∀ n v.  FLOOKUP pSt.bindings n = SOME v
                ⇒ ∃v'.  nsLookup (cEnv.v) (Short n) = SOME v' ∧
                        ^(DATUM) v v'
End

(* CHECKING CONSISTENCY BETWEEN FFI AND PAYLOAD STATE *)
Definition ffi_cor_def:
  ffi_cor cpNum pSt (fNum,fQueue,fNet) ⇔
    cpNum = fNum ∧
    ∀extproc.
      let
        pMes = FILTER (λ(n,_). n = extproc) pSt.queue;
        fMes = FILTER (λ(n,_). n = extproc) fQueue
      in  
        isPREFIX pMes fMes
End

(* FINAL DEFINITION OF A VALID PAYLOAD/CAKEML EVALUATION *)

Definition cpEval_valid_def:
  cpEval_valid conf cpNum cEnv pSt pCd vs cSt ⇔
    env_asm cEnv conf ∧
    enc_ok conf cEnv (letfuns pCd) vs ∧
    pSt_pCd_corr pSt pCd ∧
    sem_env_cor conf pSt cEnv ∧
    ffi_cor cpNum pSt cSt.ffi.ffi_state
End

(* DEFINITION OF EQUIVALENT CAKEML EVALUTATIONS *)

Definition cEval_equiv_def:
  cEval_equiv conf (csA,crA) (csB,crB) ⇔
    ffi_eq conf csA.ffi.ffi_state csB.ffi.ffi_state ∧
    crA = crB ∧
    crA ≠ Rerr (Rabort Rtimeout_error)
End

Theorem evaluate_general:
  ∀ (cSt: 'ffi semanticPrimitives$state) env ck1 ck2 refs' u. 
      evaluate (empty_state with <|clock := ck1; refs := cSt.refs|>) env
           [exp] =
         (empty_state with <|clock := ck2; refs := cSt.refs ++ refs'|>,
          Rval [u])
    ⇒ ∀mc. evaluate (cSt with clock := ck1 + mc) env [exp]
                = (cSt with <|clock := ck2 + mc;
                               refs := cSt.refs ++ refs'|>,
                   Rval [u])
Proof
  rpt strip_tac >>
  ‘evaluate (cSt with clock := ck1) env [exp]
                  = (cSt with <|clock := ck2;
                                 refs := cSt.refs ++ refs'|>,
                     Rval[u])’
    suffices_by (qspecl_then [‘cSt with clock := ck1’,
                              ‘env’, ‘[exp]’,
                              ‘cSt with <|clock := ck2;
                                 refs := cSt.refs ++ refs'|>’,
                              ‘Rval [u]’, ‘mc’]
                              assume_tac evaluate_add_to_clock >>
                 fs[]) >>
  qabbrev_tac ‘s  = empty_state with <|clock := ck1;
                                      refs   := cSt.refs|>’ >>
  qabbrev_tac ‘s' = empty_state with <|clock := ck2;
                                      refs   := cSt.refs ++ refs'|>’ >>
  qabbrev_tac ‘e = [exp]’ >>
  qabbrev_tac ‘r = Rval [u] :(v list, v) result’ >>
  ‘(evaluate s env e = (s',r)) ∧ (s'.ffi = s.ffi) ∧
    (∀outcome. r ≠ Rerr (Rabort (Rffi_error outcome))) ⇒
    ∀t : 'ffi semanticPrimitives$state.
        (t.clock = s.clock) ∧ (t.refs = s.refs) ⇒
        (evaluate t env e =
        (t with <|clock := s'.clock; refs := s'.refs|>,r))’
    by metis_tac[evaluate_ffi_intro] >>
  rfs[Abbr ‘s'’, Abbr ‘s’, Abbr ‘r’]
QED


Theorem clock_irrel:
  ∀ conf cSt1 cSt2 cEnv cExps.
    ∀mc eck1 eck2.    
      cEval_equiv conf
        (evaluate (cSt1 with clock := mc) cEnv cExps)
        (evaluate (cSt2 with clock := mc) cEnv cExps)
    ⇒ cEval_equiv conf
        (evaluate (cSt1 with clock := eck1 + mc) cEnv cExps)
        (evaluate (cSt2 with clock := eck2 + mc) cEnv cExps)
Proof
  rpt strip_tac >>
  Cases_on ‘evaluate (cSt1 with clock := mc) cEnv cExps’ >>
  Cases_on ‘evaluate (cSt2 with clock := mc) cEnv cExps’ >>
  fs[cEval_equiv_def] >>
  ‘evaluate (cSt1 with clock := eck1 + mc) cEnv cExps
    = (q with clock := eck1 + q.clock,r)’
    by (Q.ISPECL_THEN [‘(cSt1 with clock := mc)’,‘cEnv’, ‘cExps’,‘q’,‘r’,‘eck1’]
                      assume_tac evaluate_add_to_clock >>
        rfs[]) >>
  ‘evaluate (cSt2 with clock := eck2 + mc) cEnv cExps
    = (q' with clock := eck2 + q'.clock,r')’
    by (Q.ISPECL_THEN [‘(cSt2 with clock := mc)’,‘cEnv’, ‘cExps’,‘q'’,‘r'’,‘eck2’]
                      assume_tac evaluate_add_to_clock >>
        rfs[]) >>
  rw[cEval_equiv_def]
QED

Theorem ffi_irrel:
  ∀conf se cpNum cEnv pSt pCd vs cSt1 cSt2.
    cpEval_valid conf cpNum cEnv pSt pCd vs cSt1 ∧
    cpEval_valid conf cpNum cEnv pSt pCd vs cSt2 ∧
    ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state
    ⇒ ∃mc. cEval_equiv conf
            (evaluate (cSt1  with clock := mc) cEnv
                      [compile_endpoint conf vs  pCd])
            (evaluate (cSt2  with clock := mc) cEnv
                      [compile_endpoint conf vs  pCd])
Proof
  Induct_on ‘pCd’
  >- (rw[compile_endpoint_def,evaluate_def,do_con_check_def,
         build_conv_def, cEval_equiv_def])
  >- (rw[compile_endpoint_def,evaluate_def] >>
      ‘∃sv. FLOOKUP pSt.bindings s = SOME sv’
        by fs[cpEval_valid_def,pSt_pCd_corr_def] >>
      ‘∃z. nsLookup cEnv.v (Short s) = SOME z ∧
           LIST_TYPE WORD sv z’
        by fs[cpEval_valid_def,sem_env_cor_def] >>
      simp[cEval_equiv_def] >>
      ‘has_v cEnv.v conf.length (LIST_TYPE ^WORD8 --> NUM) LENGTH’
        by fs[cpEval_valid_def,env_asm_def] >>
      fs[has_v_def,Arrow_def,AppReturns_def] >>
      pop_assum (drule_then assume_tac) >>
      first_assum (qspec_then ‘cSt1.refs’ assume_tac) >>
      first_assum (qspec_then ‘cSt2.refs’ assume_tac) >>
      fs[] >> Q.REFINE_EXISTS_TAC ‘SUC mc’ >> simp[] >>
      fs[eval_rel_def] >>
      simp[dec_clock_def] >>
      Q.REFINE_EXISTS_TAC ‘ck1 + ck1' + mc’ >>
      ‘∀mc. evaluate (cSt1 with clock := ck1 + ck1' + mc) env [exp]
            = (cSt1 with <|clock := ck2 + ck1' + mc;
                           refs := cSt1.refs ++ refs'|>,
               Rval [u])’
        by (strip_tac >>
            ‘ck1 + ck1' + mc = ck1 + (ck1' + mc)’
              by simp[] >>
            first_x_assum SUBST1_TAC >>
            ‘ck2 + ck1' + mc = ck2 + (ck1' + mc)’
              by simp[] >>
            first_x_assum SUBST1_TAC >>
            metis_tac[evaluate_general]) >>
      ‘∀mc. evaluate (cSt2 with clock := ck1 + ck1' + mc) env [exp]
            = (cSt2 with <|clock := ck2' + ck1 + mc;
                           refs := cSt2.refs ++ refs''|>,
               Rval [u'])’
        by (strip_tac >>
            ‘ck1 + ck1' + mc = ck1' + (ck1 + mc)’
              by simp[] >>
            first_x_assum SUBST1_TAC >>
            ‘ck2' + ck1 + mc = ck2' + (ck1 + mc)’
              by simp[] >>
            first_x_assum SUBST1_TAC >>
            metis_tac[evaluate_general]) >>
      simp[] >>
      rw[do_app_def] >>
      fs[NUM_def,INT_def] >>
      simp[do_if_def, Boolv_def, opb_lookup_def] >>
      Cases_on ‘LENGTH sv ≤ n’ >> simp[]
      >- (last_x_assum (qspecl_then [‘conf’,‘cpNum’,‘cEnv’,
                                    ‘pSt’,‘vs’,
                                    ‘cSt1 with refs := cSt1.refs ++ refs'’,
                                    ‘cSt2 with refs := cSt2.refs ++ refs''’]
                                  assume_tac) >>
          rfs[cpEval_valid_def,letfuns_def] >>
          ‘pSt_pCd_corr pSt pCd’
            by fs[pSt_pCd_corr_def,Once pFv_def] >>
          fs[] >>
          qexists_tac ‘mc’ >>
          ‘cSt1 with <|clock := ck1' + (ck2 + mc); refs := cSt1.refs ++ refs';
                       ffi := cSt1.ffi|> =
           cSt1 with <|clock := ck1' + (ck2 + mc); refs := cSt1.refs ++ refs'|>’
            by simp[state_component_equality] >>
          first_x_assum SUBST1_TAC >>
          ‘cSt2 with <|clock := ck1 + (ck2' + mc); refs := cSt2.refs ++ refs'';
                       ffi := cSt2.ffi|> =
           cSt2 with <|clock := ck1 + (ck2' + mc); refs := cSt2.refs ++ refs''|>’
            by simp[state_component_equality] >>
          first_x_assum SUBST1_TAC >>
          ‘ck1' + (ck2  + mc) = (ck1' + ck2 ) + mc’
            by simp[] >>
          first_x_assum SUBST1_TAC >>
          ‘ck1  + (ck2' + mc) = (ck1  + ck2') + mc’
            by simp[] >>
          first_x_assum SUBST1_TAC >>
          qspecl_then [‘conf’,‘cSt1 with refs := cSt1.refs ++ refs'’,
                       ‘cSt2 with refs := cSt2.refs ++ refs''’, ‘cEnv’,
                       ‘[compile_endpoint conf vs pCd]’,
                       ‘mc’, ‘ck1' + ck2’, ‘ck1 + ck2'’]
                      assume_tac clock_irrel >>
          rfs[])
      >- (ntac 2 (ONCE_REWRITE_TAC [evaluate_def]) >>
          ‘ALL_DISTINCT (MAP (λ(x,y,z). x) (sendloop conf (MAP (CHR ∘ w2n) l)))’
            by EVAL_TAC >>
          simp[] >>
          rw[sendloop_correct] >>              
          cheat)
      )
  >- (cheat)
  >- (cheat)
  >- (cheat)
QED

val _ = export_theory ();