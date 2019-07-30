open preamble
     endpoint_to_payloadTheory (* for compile_message only*)
     payloadLangTheory payload_to_cakemlTheory
     evaluateTheory terminationTheory ml_translatorTheory ml_progTheory evaluatePropsTheory
     namespaceTheory
     semanticPrimitivesTheory
     ffiTheory
     comms_ffi_modelTheory
     comms_ffi_toolsTheory
     payloadPropsTheory
     payloadSemanticsTheory
     evaluate_rwLib
     state_tacticLib
     evaluate_toolsTheory
     ckExp_EquivTheory
     optionTheory
     rich_listTheory
     bisimulationTheory;

val _ = new_theory "payload_to_cakemlProof";

val JSPEC_THEN =
  fn spTr => fn nxTc => fn spTh => 
    FIRST[qspec_then spTr nxTc spTh, Q.ISPEC_THEN spTr nxTc spTh];

fun JSPECL_THEN []            = (fn nxTc => (fn spTh => nxTc spTh))
  | JSPECL_THEN (spTr::spTrs) =
    (fn nxTc =>
      (fn spTh =>
        let
          val recFunc = (JSPECL_THEN spTrs nxTc)
        in
          JSPEC_THEN spTr recFunc spTh
        end)
    ); 

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
    has_v env.c conf.nil  $= (0,TypeStamp "[]" list_type_num) ∧
    has_v env.c conf.cons $= (2,TypeStamp "::" list_type_num) ∧
    has_v env.v conf.concat (LIST_TYPE ^WORD8 --> LIST_TYPE ^WORD8 --> LIST_TYPE ^WORD8) $++ ∧ 
    has_v env.v conf.length (LIST_TYPE ^WORD8 --> NUM) LENGTH ∧
    has_v env.v conf.null (LIST_TYPE ^WORD8 --> BOOL) NULL ∧
    has_v env.v conf.take (LIST_TYPE ^WORD8 --> NUM --> LIST_TYPE ^WORD8) (combin$C TAKE) ∧
    has_v env.v conf.drop (LIST_TYPE ^WORD8 --> NUM --> LIST_TYPE ^WORD8) (combin$C DROP) ∧
    (∃v. nsLookup env.v conf.toList = SOME v ∧
         (∀s1:unit semanticPrimitives$state l ll.
           store_lookup ll s1.refs = SOME (W8array l)
            ⇒ ∃env' exp ck1 ck2 lv.
              do_opapp [v; Loc ll] = SOME(env',exp)           ∧
              evaluate (s1 with clock := ck1) env' [exp] =
                (s1 with <|clock := ck2|>,Rval [lv])      ∧
              LIST_TYPE ^WORD8 l lv)) ∧
    (∃v. nsLookup env.v conf.fromList = SOME v ∧
         (∀l lv.
           LIST_TYPE ^WORD8 l lv
           ⇒ ∀s1: unit semanticPrimitives$state. ∃env' exp ck1 ck2. do_opapp [v; lv] = SOME(env',exp)
               ∧ evaluate (s1 with clock := ck1) env' [exp] =
                  (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,Rval [Loc(LENGTH s1.refs)]))) ∧
    in_module conf.nil ∧
    in_module conf.cons ∧
    in_module conf.concat ∧
    in_module conf.length ∧
    in_module conf.null ∧
    in_module conf.take ∧
    in_module conf.drop ∧
    in_module conf.fromList ∧
    in_module conf.toList)
End


Theorem remove_ffi[simp]:
  ∀cSt: 'ffi semanticPrimitives$state.
    (cSt with ffi := cSt.ffi) = cSt
Proof
  simp[state_component_equality]
QED

Theorem remove_refs[simp]:
  ∀cSt: 'ffi semanticPrimitives$state.
    (cSt with refs := cSt.refs) = cSt
Proof
  simp[state_component_equality]
QED

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

Theorem find_one_equiv:
  ∀env lnum s1 l n. 
    nsLookup     env.v (Short "x") = SOME (Loc lnum) ∧
    store_lookup lnum  s1.refs     = SOME (W8array l) ⇒
    ∃ck1 ck2 drefs_f rv.
      evaluate$evaluate (s1 with clock := ck1) env
                      [Letrec find_one
                        (App Opapp [Var (Short "find_one");
                                    Lit (IntLit &n)])]
      = (s1 with <|clock := ck2; refs := s1.refs ++ drefs_f|>,
         Rval [rv]) ∧
      NUM (hfind_one n l) rv
Proof
  rw[] >>
  completeInduct_on ‘LENGTH l - n’ >>
  rw (find_one_def::(Once find_recfun_def)::eval_sl) >>
  qmatch_goalsub_abbrev_tac ‘App Opapp [Var (Short "find_one"); rec_value]’ >>
  qabbrev_tac ‘rec_call = App Opapp [Var (Short "find_one"); rec_value]’ >>
  qunabbrev_tac ‘rec_value’ >>
  Q.REFINE_EXISTS_TAC ‘SUC ck1’ >> rw (ADD1::dec_clock_def::eval_sl)
  >- (‘LENGTH l ≤ n’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw (Once hfind_one_def::trans_sl) >>
      MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >>
      rw[])
  >- (‘LENGTH l > n’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw (Once hfind_one_def::(trans_sl@eval_sl)) >> fs[]
      >- (MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >> rw[])
      >- (rpt (qpat_x_assum ‘T’ (K ALL_TAC)) >>
          first_x_assum (qspec_then ‘LENGTH l - (n + 1)’ assume_tac) >>
          rfs[] >>
          first_x_assum (qspecl_then [‘l’,‘n + 1’] assume_tac) >>
          rfs(ADD1::store_lookup_def::trans_sl)  >>
          MAP_EVERY qexists_tac [‘ck1’,‘ck2’,‘drefs_f’] >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m envM _’ >>
          qmatch_asmsub_abbrev_tac ‘evaluate s1m env [irecexp]’ >>
          ‘evaluate s1m envM [rec_call] = evaluate s1m env [irecexp]’
            suffices_by rw[] >>
          qpat_x_assum ‘evaluate s1m env [irecexp] = _’ (K ALL_TAC) >>
          qunabbrev_tac ‘irecexp’ >>
          qunabbrev_tac ‘rec_call’ >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m envM IGNORE’ >>
          qmatch_goalsub_abbrev_tac ‘evaluate s1m env [Letrec find_one IGNORE2]’ >>
          rw eval_sl
          >- (EVAL_TAC >>
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
              intLib.COOPER_TAC)
          >- (‘ALL_DISTINCT (MAP (λ(x,y,z). x) find_one)’
                suffices_by fs[] >>
              EVAL_TAC)))
  >- (Cases_on ‘LENGTH l ≤ n’ >> fs eval_sl)
QED 

Theorem find_one_correct:
  ∀env lnum s1 h l. 
    nsLookup     env.v (Short "x") = SOME (Loc lnum) ∧
    store_lookup lnum  s1.refs     = SOME (W8array (h::l)) ⇒
    ∃ck1 ck2 drefs_f rv.
      evaluate$evaluate (s1 with clock := ck1) env
                      [Letrec find_one
                        (App Opapp [Var (Short "find_one");
                                    Lit (IntLit &1)])]
      = (s1 with <|clock := ck2; refs := s1.refs ++ drefs_f|>,
         Rval [rv]) ∧
      NUM (1 + LENGTH (FST (SPLITP ($=1w) l))) rv
Proof
  rw[] >>
  ‘1 + LENGTH (FST (SPLITP ($=1w) l)) = hfind_one 1 (h::l)’
    suffices_by (rw[] >> metis_tac[find_one_equiv]) >>
  Cases_on ‘LENGTH l = 0’
  >- (Cases_on ‘l’ >> fs[LENGTH_NIL,SPLITP,Once hfind_one_def]) >>
  ‘0 < LENGTH l’
    by simp[] >>
  qpat_x_assum ‘LENGTH l ≠ 0’ (K ALL_TAC) >>
  ‘∀n (l : word8 list). n < LENGTH l ⇒ hfind_one n l = n + LENGTH (FST (SPLITP ($=1w) (DROP n l)))’
    suffices_by (rw[] >> first_x_assum (assume_tac o REWRITE_RULE [Once EQ_SYM_EQ]) >>
                 first_x_assum (qspecl_then [‘1’,‘h::l’] assume_tac)) >>
  rpt (first_x_assum (K ALL_TAC)) >>
  rw[] >>
  Induct_on ‘LENGTH l - n’
  >- rw[Once hfind_one_def,DROP_LENGTH_TOO_LONG,SPLITP,FST]
  >- (rw[Once hfind_one_def] >>
      ‘DROP n l = (EL n l)::(DROP (SUC n) l)’
        by (irule DROP_CONS_EL >> fs[])
      >- rw[Once SPLITP]
      >- (first_x_assum (JSPECL_THEN [‘l’,‘SUC n’] assume_tac) >>
          rfs[] >>
          Cases_on ‘SUC n < LENGTH l’
          >- (fs[] >> rw[Once SPLITP])
          >- (rw[Once SPLITP] >>
              ‘DROP (SUC n) l = []’
                by (irule DROP_LENGTH_TOO_LONG >> fs[]) >>
              fs[SPLITP,FST,LENGTH_NIL] >>
              rw[Once hfind_one_def])))
QED


Theorem unpadv_correct:
 ∀env conf l le lnum s1 s2 refs.
  env_asm env conf ∧
  evaluate$evaluate s1 env [le] = (s2 with refs := s1.refs ++ refs, Rval [Loc lnum]) ∧
  store_lookup lnum (APPEND s1.refs refs) = SOME(W8array l) ∧
  LENGTH l > 0
  ⇒
  ∃ck1 ck2 refs' num ulv.
  evaluate$evaluate (s1 with clock:= ck1) env [App Opapp [unpadv conf; le]] =
           (s2 with <|clock := ck2; refs := APPEND s1.refs refs'|>, Rval [ulv]) ∧
  LIST_TYPE ^WORD8 (unpad l) ulv
Proof
  rpt strip_tac >>
  rw[unpadv_def,validv_def,finalv_def] >>
  qabbrev_tac ‘FEXP = App Opapp [Var conf.toList; Var (Short "y")]’ >>
  qabbrev_tac ‘BEXP = Letrec find_one (App Opapp [Var (Short "find_one"); Lit (IntLit 1)])’ >>
  ‘∃h t. l = h::t’
    by (Cases_on ‘l’ >> fs[LENGTH]) >>
  rw(unpad_def::eval_sl) >>
  drule_then strip_assume_tac evaluate_add_to_clock >>
  fs[] >> Q.REFINE_EXISTS_TAC ‘ck1 + s1.clock’ >>
  simp[] >> Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
  rw[ADD1,dec_clock_def] >> rw eval_sl >>
  ‘¬((&SUC (LENGTH t) :int) - 1 < 0)’
        by (qmatch_goalsub_abbrev_tac ‘¬(SLT - 1 < 0)’ >>
            ‘1 ≤ SLT’
                suffices_by metis_tac[integerTheory.INT_NOT_LE,
                                      integerTheory.INT_SUB_LE,
                                      integerTheory.INT_LE] >>
            qunabbrev_tac ‘SLT’ >> rw[realTheory.REAL]) >>
  fs (store_lookup_def::terminationTheory.do_eq_def::eval_sl)
  >- (rw eval_sl
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC)
      >- (qabbrev_tac ‘TOG = s1.refs ++ refs’ >>
          ‘LENGTH refs + LENGTH s1.refs = LENGTH TOG’
            by rw[Abbr ‘TOG’,LENGTH_APPEND] >>
          fs[EL_LENGTH_APPEND,EL_APPEND_EQN] >>
          ‘Num (ABS (1 + &Num (ABS (&SUC (LENGTH t) − 1)))) = SUC (LENGTH t)’
            by (qmatch_goalsub_abbrev_tac ‘1 + &Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >>
                ‘&Num SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_OF_NUM] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >> rw[]) >>
          rw[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate (s2M with clock := _) envM [FEXP]’ >>
          ‘env_asm envM conf’
            by (qunabbrev_tac ‘envM’ >>
                fs[env_asm_def,has_v_def,in_module_def]) >>
          qunabbrev_tac ‘FEXP’ >>
          rw[evaluate_def] >>
          qunabbrev_tac ‘envM’ >>
          rw[nsLookup_def,nsBind_def,nsLookup_nsBind_compute] >>
          qmatch_asmsub_abbrev_tac ‘env_asm (env with v:= envMv) conf’ >>
          qpat_x_assum ‘env_asm (env with v:= envMv) conf’
                       (assume_tac o REWRITE_RULE [env_asm_def]) >>
          qmatch_asmsub_abbrev_tac ‘_ ∧ has_v _ conf.drop _ _ ∧ toThing ∧ _’ >>
          ‘toThing’
            by (qunabbrev_tac ‘toThing’ >> fs[]) >>
          qunabbrev_tac ‘toThing’ >>
          qpat_x_assum ‘has_v _ _ _ _ ∧ _’
                       (assume_tac o REWRITE_RULE [GSYM env_asm_def]) >>
          fs[] >>
          Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
          rw[ADD1,dec_clock_def] >>
          ‘store_lookup (LENGTH TOG) (empty_state with refs := s2M.refs).refs =
            SOME (W8array t)’
            by (qunabbrev_tac ‘s2M’ >> rw[store_lookup_def] >>
                rw[EL_LENGTH_APPEND] >>
                qmatch_goalsub_abbrev_tac ‘&Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >>
                rw[integerTheory.INT,int_arithTheory.elim_minus_ones] >>
                rw[DROP_REPLICATE]) >>
          first_x_assum (drule_then strip_assume_tac) >>
          rw[] >>
          qunabbrev_tac ‘s2M’ >> qunabbrev_tac ‘TOG’ >>
          qmatch_asmsub_rename_tac ‘evaluate (empty_state with <| clock := ck1; refs := _|>)
                                             senv [sexp] =
                                      (empty_state with <| clock := ck2; refs := _ |>,Rval[ulv])’ >>
          fs[] >>
          qmatch_asmsub_abbrev_tac ‘evaluate _ _ _ = (empty_state with <|clock := ck2; refs := s1.refs ++ ex_refs1 ++ ex_refs2|>,_)’ >>
          MAP_EVERY qexists_tac [‘ck1’,‘ck2 + s2.clock’,‘ex_refs1 ++ ex_refs2’,‘ulv’] >>
          JSPECL_THEN [‘s2 with refs := s1.refs ++ ex_refs1 ++ ex_refs2’,
                       ‘senv’,‘sexp’,‘ck1’,‘ck2’,‘[]’,‘ulv’] strip_assume_tac
                       evaluate_generalise >>
          rfs[])
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC))
  >- (rw eval_sl
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC)
      >- (qabbrev_tac ‘TOG = s1.refs ++ refs’ >>
          ‘LENGTH refs + LENGTH s1.refs = LENGTH TOG’
            by rw[Abbr ‘TOG’,LENGTH_APPEND] >>
          fs[EL_LENGTH_APPEND,EL_APPEND_EQN] >>
          ‘Num (ABS (1 + &Num (ABS (&SUC (LENGTH t) − 1)))) = SUC (LENGTH t)’
            by (qmatch_goalsub_abbrev_tac ‘1 + &Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >>
                ‘&Num SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_OF_NUM] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >> rw[]) >>
          rw[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate (s2M with clock := _) envM [FEXP]’ >>
          ‘env_asm envM conf’
            by (qunabbrev_tac ‘envM’ >>
                fs[env_asm_def,has_v_def,in_module_def]) >>
          qunabbrev_tac ‘FEXP’ >>
          rw[evaluate_def] >>
          qunabbrev_tac ‘envM’ >>
          rw[nsLookup_def,nsBind_def,nsLookup_nsBind_compute] >>
          qmatch_asmsub_abbrev_tac ‘env_asm (env with v:= envMv) conf’ >>
          qpat_x_assum ‘env_asm (env with v:= envMv) conf’
                       (assume_tac o REWRITE_RULE [env_asm_def]) >>
          qmatch_asmsub_abbrev_tac ‘_ ∧ has_v _ conf.drop _ _ ∧ toThing ∧ _’ >>
          ‘toThing’
            by (qunabbrev_tac ‘toThing’ >> fs[]) >>
          qunabbrev_tac ‘toThing’ >>
          qpat_x_assum ‘has_v _ _ _ _ ∧ _’
                       (assume_tac o REWRITE_RULE [GSYM env_asm_def]) >>
          fs[] >>
          Q.REFINE_EXISTS_TAC ‘SUC ck1’ >>
          rw[ADD1,dec_clock_def] >>
          ‘store_lookup (LENGTH TOG) (empty_state with refs := s2M.refs).refs =
            SOME (W8array t)’
            by (qunabbrev_tac ‘s2M’ >> rw[store_lookup_def] >>
                rw[EL_LENGTH_APPEND] >>
                qmatch_goalsub_abbrev_tac ‘&Num (ABS SLT)’ >>
                ‘ABS SLT = SLT’
                  by (‘0 ≤ SLT’
                        suffices_by metis_tac[integerTheory.INT_ABS_EQ_ID] >>
                      metis_tac[integerTheory.INT_NOT_LE]) >>
                rw[] >> qunabbrev_tac ‘SLT’ >>
                rw[integerTheory.INT,int_arithTheory.elim_minus_ones] >>
                rw[DROP_REPLICATE]) >>
          first_x_assum (drule_then strip_assume_tac) >>
          rw[] >>
          qunabbrev_tac ‘s2M’ >> qunabbrev_tac ‘TOG’ >>
          qmatch_asmsub_rename_tac ‘evaluate (empty_state with <| clock := ck1; refs := _|>)
                                             senv [sexp] =
                                      (empty_state with <| clock := ck2; refs := _ |>,Rval[ulv])’ >>
          fs[] >>
          qmatch_asmsub_abbrev_tac ‘evaluate _ _ _ = (empty_state with <|clock := ck2; refs := s1.refs ++ ex_refs1 ++ ex_refs2|>,_)’ >>
          MAP_EVERY qexists_tac [‘ck1’,‘ck2 + s2.clock’,‘ex_refs1 ++ ex_refs2’,‘ulv’] >>
          JSPECL_THEN [‘s2 with refs := s1.refs ++ ex_refs1 ++ ex_refs2’,
                       ‘senv’,‘sexp’,‘ck1’,‘ck2’,‘[]’,‘ulv’] strip_assume_tac
                       evaluate_generalise >>
          rfs[])
      >- (‘F’ suffices_by simp[] >>
          ‘1 = 1 + (&SUC (LENGTH t) : int)’
            by (CCONTR_TAC >> fs eval_sl) >>
          intLib.COOPER_TAC))
  >- (qmatch_goalsub_abbrev_tac ‘evaluate (SE with clock := _) EE’ >>
      JSPECL_THEN [‘EE’,‘lnum’,‘SE’,‘6w’,‘t’] strip_assume_tac find_one_correct >>
      qunabbrev_tac ‘SE’ >> qunabbrev_tac ‘EE’ >> rfs[store_lookup_def] >>
      drule_then strip_assume_tac evaluate_add_to_clock >>
      fs trans_sl >>
      Q.REFINE_EXISTS_TAC ‘ck1 + ck1f’ >>
      simp[] >>
      qabbrev_tac ‘TOG = s1.refs ++ refs’ >>
      ‘LENGTH refs + LENGTH s1.refs = LENGTH TOG’
        by rw[Abbr ‘TOG’,LENGTH_APPEND] >>
      fs[EL_LENGTH_APPEND,EL_APPEND_EQN] >>
      rw eval_sl
      >- (fs[env_asm_def,has_v_def] >>
          qunabbrev_tac ‘TOG’ >>
          MAP_EVERY qexists_tac [‘0’,‘ck2+s2.clock’,‘refs ++ drefs_f’] >>
          simp[] >>
          ‘LENGTH (FST (SPLITP ($= 1w) t)) = LENGTH t’
            by (CCONTR_TAC >> fs(ADD1::eval_sl)) >>
          ‘LENGTH (SND (SPLITP ($= 1w) t)) = 0’
            by (‘LENGTH t +
                 LENGTH (SND (SPLITP ($=1w) t)) =
                 LENGTH t’
                  by metis_tac[SPLITP_LENGTH] >>
                fs[]) >>
          Cases_on ‘SPLITP ($= 1w) t’ >> fs (list_type_num_def::trans_sl))
      >- (‘LENGTH (FST (SPLITP ($=1w) t)) + 1 < SUC (LENGTH t)’
            by (‘LENGTH (FST (SPLITP ($=1w) t)) + 1 ≠ SUC (LENGTH t)’
                  by (CCONTR_TAC >> fs eval_sl) >>
                ‘∀ (l:word8 list). LENGTH (FST (SPLITP ($=1w) l)) ≤ LENGTH l’
                  suffices_by (rw[] >> first_x_assum (qspec_then ‘t’ assume_tac) >>
                               fs[ADD1]) >>
                Induct_on ‘l’ >> 
                rw[SPLITP]) >>
          rw[EL_LENGTH_APPEND,EL_APPEND_EQN]
          >- (intLib.COOPER_TAC) >>
          simp[integerTheory.INT_OF_NUM,integerTheory.INT_ABS_NUM,
               integerTheory.INT_ADD, integerTheory.INT_SUB,ADD1] >>
          qunabbrev_tac ‘FEXP’ >>
          fs[env_asm_def,in_module_def] >>
          PURE_ONCE_REWRITE_TAC [evaluate_def] >>
          rw eval_sl_nf >>
          qmatch_goalsub_abbrev_tac ‘LUPDATE (W8array l) ll os’ >>
          last_x_assum (qspecl_then [‘empty_state with refs :=
                                        LUPDATE (W8array l) ll os’,
                                     ‘l’,‘ll’] strip_assume_tac) >>
          rpt (qpat_x_assum ‘has_v _ _ _ _’ (K ALL_TAC)) >>
          rpt (qpat_x_assum ‘∀a. _’ (K ALL_TAC)) >>
          rpt (qpat_x_assum ‘nsLookup _ _ = _’ (K ALL_TAC)) >>
          qunabbrev_tac ‘ll’ >> qunabbrev_tac ‘os’ >>
          rfs[store_lookup_def,EL_LENGTH_APPEND,EL_APPEND_EQN,
              EL_LUPDATE] >>
          Q.REFINE_EXISTS_TAC ‘SUC ck1f’ >>
          rw[ADD1,dec_clock_def] >>
          qmatch_goalsub_abbrev_tac
            ‘evaluate (s2c with clock := _) envE [expE] = (_,_)’ >>
          qmatch_asmsub_rename_tac ‘evaluate (empty_state with
                                                <| clock := Ack1;
                                                   refs := _|>)
                                              _ _ =
                                              (empty_state with
                                                <| clock := Ack2;
                                                   refs := _|>,
                                              Rval[vE])’ >>
          JSPECL_THEN [‘s2c’,‘envE’,‘expE’,‘Ack1’,‘Ack2’,‘[]’,‘vE’]
                      strip_assume_tac evaluate_generalise >>
          qunabbrev_tac ‘s2c’ >> rfs[] >>
          Q.REFINE_EXISTS_TAC ‘Ack1 + ck1f’ >>
          simp[] >>
          qunabbrev_tac ‘TOG’ >>
          MAP_EVERY qexists_tac [‘0’,‘Ack2 + ck2 + s2.clock’,
                                 ‘refs ++ drefs_f ++ [W8array l]’] >>
          qmatch_goalsub_abbrev_tac ‘s2 with <| clock := _; refs := r1 |> =
                                     s2 with <| clock := _; refs := r2 |>’ >>
          rw[state_component_equality]
          >- (qunabbrev_tac ‘r1’ >> qunabbrev_tac ‘r2’ >>
              rpt (first_x_assum (K ALL_TAC)) >>
              qabbrev_tac ‘rj = s1.refs ++ refs ++ drefs_f’ >>
              ‘LENGTH (s1.refs ++ refs) + LENGTH drefs_f = LENGTH rj’
                by (qunabbrev_tac ‘rj’ >> simp[LENGTH_APPEND]) >>
              rw[])
          >- (qmatch_goalsub_abbrev_tac ‘LIST_TYPE WORD ol vE’ >>
              ‘ol = l’
                suffices_by rw[] >>
              qunabbrev_tac ‘ol’ >> qunabbrev_tac ‘l’ >>
              rpt (first_x_assum (K ALL_TAC)) >>
              rw[DROP_LENGTH_TOO_LONG,LENGTH_REPLICATE] >>
              Induct_on ‘t’ >> simp [SPLITP] >>
              rw[] >> Cases_on ‘1w = h’ >> simp[] >> fs[ADD1] >>
              Cases_on ‘SPLITP ($= 1w) t’ >> fs[]))
      >- (Cases_on ‘LENGTH (FST (SPLITP ($= 1w) t)) + 1 = SUC (LENGTH t)’ >>
          fs trans_sl))
  >- (fs[env_asm_def,has_v_def] >>
      MAP_EVERY qexists_tac [‘0’,‘s2.clock’,‘refs’] >>
      rw (list_type_num_def::trans_sl))
QED


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

Definition valid_send_event_format_def:
  valid_send_event_format conf dest event =
    case event of
      IO_event n d c =>
         (valid_send_call_format conf dest n d (MAP FST c) ∧
          (MAP FST c = MAP SND c))
End

Theorem LUPDATE_SAME':
  n < LENGTH ls ∧ EL n ls = a ⇒ LUPDATE a n ls = ls
Proof
  metis_tac[LUPDATE_SAME]
QED

Theorem sendloop_correct:
  ∀conf l env env' aexp s stpred dest.
  env_asm env' conf ∧
  conf.payload_size ≠ 0 ∧
  nsLookup env.v (Short "sendloop") = SOME(Recclosure env' (sendloop conf (MAP (CHR o w2n) dest)) "sendloop") ∧
  ck_equiv_hol env (LIST_TYPE ^WORD8) aexp l ∧
  stpred s.ffi.ffi_state ∧
  ffi_accepts_rel stpred (valid_send_call_format conf dest) s.ffi.oracle
  ⇒
  ∃ck1 ck2 refs' num lv'.
  evaluate$evaluate (s with clock:= ck1) env [App Opapp [Var (Short "sendloop"); aexp]] =
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
  ntac 3 (simp[Once evaluate_def]) >>
  drule_then (JSPEC_THEN ‘s’ strip_assume_tac) ck_equiv_hol_apply >>
  Q.REFINE_EXISTS_TAC ‘bc1 + ck1’ >>
  simp[do_opapp_def] >> 
  first_x_assum (K ALL_TAC) >>
  ntac 2 (simp[Once sendloop_def]) >>
  simp[find_recfun_def] >>
  Q.REFINE_EXISTS_TAC ‘extra + 1’ >>
  simp[dec_clock_def] >>
  simp[Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ env1’ >>
  ‘env_asm env1 conf’
    by fs[Abbr ‘env1’,env_asm_def,build_rec_env_def,sendloop_def,has_v_def,in_module_def] >>
  drule padv_correct >> disch_then drule >>
  disch_then(qspecl_then [‘Var (Short "x")’,‘s with refs := s.refs ++ drefs’,‘s’,‘[]’] mp_tac) >>
  impl_tac >- simp[evaluate_def,Abbr ‘env1’,semanticPrimitivesTheory.state_component_equality] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘clock_fupd (K ack1)’ >>
  Q.REFINE_EXISTS_TAC ‘extra + ack1’ >>
  dxrule evaluate_add_to_clock >>
  simp[] >> disch_then kall_tac >>
  unite_nums "dc" >>
  ntac 4 (simp[Once evaluate_def]) >>  
  simp[ml_progTheory.nsLookup_nsBind_compute,namespaceTheory.nsOptBind_def,
       do_app_def,ffiTheory.call_FFI_def] >>
  simp[Once evaluate_def] >>
  qhdtm_assum ‘ffi_accepts_rel’
              (mp_tac o REWRITE_RULE [valid_send_call_format_def,
                                      ffi_accepts_rel_def]) >>
  disch_then drule >> simp[] >>
  disch_then(qspec_then ‘pad conf l’ mp_tac) >>
  impl_keep_tac >- rw[pad_def] >>
  strip_tac >>
  simp[IMPLODE_EXPLODE_I,MAP_MAP_o,o_DEF,
       SIMP_RULE std_ss [o_DEF] n2w_ORD_CHR_w2n] >>
  fs[store_assign_def,store_lookup_def,store_v_same_type_def,
     LUPDATE_SAME'] >>
  simp[payload_size_def] >>
  qabbrev_tac ‘LEN_EXP = App Opapp [Var conf.length; Var (Short "x")]’ >>
  qabbrev_tac ‘DRP_EXP = App Opapp [App Opapp [Var conf.drop; Var (Short "x")]; Lit (IntLit (&conf.payload_size))]’ >>
  rw eval_sl >>
  qmatch_goalsub_abbrev_tac ‘evaluate _ env2’ >>
  qmatch_goalsub_abbrev_tac ‘evaluate (s2 with clock := _) _’ >>
  ‘env_asm env2 conf’
    by fs[Abbr ‘env2’,env_asm_def,build_rec_env_def,sendloop_def,has_v_def,in_module_def] >>
  ‘ck_equiv_hol env2 NUM LEN_EXP (LENGTH l)’
    by (qunabbrev_tac ‘LEN_EXP’ >> irule ck_equiv_hol_App >>
        qexists_tac ‘LIST_TYPE ^WORD8’ >> strip_tac
        >- (irule ck_equiv_hol_Var >> qexists_tac ‘cV’ >>
            simp[Abbr ‘env2’,ml_progTheory.nsLookup_nsBind_compute])
        >- (irule ck_equiv_hol_Var >>
           fs[env_asm_def,in_module_def,has_v_def])) >>
  drule_then (JSPEC_THEN ‘s2’ strip_assume_tac) ck_equiv_hol_apply >>
  rename [‘∀dc. evaluate (s2 with clock := bc1 + dc) _ _ =
               (s2 with <|clock:= dc + bc2; refs := s2.refs ++ drefsL|>,
                Rval [cVL])’] >>
  Q.REFINE_EXISTS_TAC ‘bc1 + extra’ >>
  simp[] >>
  first_x_assum (K ALL_TAC) >>
  fs trans_sl >>
  ntac 2 (first_x_assum (K ALL_TAC)) >>
  qpat_x_assum ‘Abbrev (LEN_EXP = _)’ (K ALL_TAC) >>
  qabbrev_tac ‘SND_EXP = App Opapp [Var (Short "sendloop"); Var (Short "x")]’ >>
  rw eval_sl
  >- (simp[Abbr ‘s2’,state_component_equality] >>
      ‘LENGTH l ≤ conf.payload_size’
        by (CCONTR_TAC >> fs eval_sl) >>
      rw[update_state_def,send_events_def] >>
      ‘final (pad conf l)’
        by (rw[final_def,pad_def]) >>
      PURE_ONCE_REWRITE_TAC [compile_message_def] >>
      simp[] >>
      ‘ffi = update_state s.ffi.ffi_state
                          s.ffi.oracle
                          [IO_event "send" dest (ZIP (pad conf l,pad conf l))]’
        suffices_by simp[state_component_equality] >>
      rw[update_state_def,send_events_def])
  >- (first_x_assum (K ALL_TAC) >>
      ‘LENGTH l > conf.payload_size’
        by (CCONTR_TAC >> fs eval_sl) >>
      ‘¬final (pad conf l)’
        by (rw[final_def,pad_def]) >>
      ‘ck_equiv_hol env2 (LIST_TYPE ^WORD8) DRP_EXP (combin$C DROP l conf.payload_size)’
        by (qunabbrev_tac ‘DRP_EXP’ >> irule ck_equiv_hol_App >>
            qexists_tac ‘NUM’ >> strip_tac
            >- (irule ck_equiv_hol_Lit >> rw trans_sl)
            >- (irule ck_equiv_hol_App >> qexists_tac ‘LIST_TYPE ^WORD8’ >> strip_tac
                >- (irule ck_equiv_hol_Var >> qexists_tac ‘cV’ >>
                    simp[Abbr ‘env2’,ml_progTheory.nsLookup_nsBind_compute])
                >- (irule ck_equiv_hol_Var >>
                    fs[env_asm_def,in_module_def,has_v_def]))) >>
      unite_nums "dc" >>
      drule_then (JSPEC_THEN
                 ‘s2 with refs := s2.refs ++ drefsL’
              strip_assume_tac) ck_equiv_hol_apply >>
      rpt (qpat_x_assum ‘ck_equiv_hol _ _ _ _’ (K ALL_TAC)) >>
      fs[] >>
      rename [‘∀dc. evaluate (s2 with <|clock := bc1 + dc; refs := s2.refs ++ drefsL|>) _ _ =
               (s2 with <|clock:= bc2 + dc; refs := s2.refs ++ drefsL ++ drefsD|>,
                Rval [cVD])’] >>
      Q.REFINE_EXISTS_TAC ‘bc1 + extra’ >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (s3 with clock := _) env3’ >>
      last_x_assum (JSPECL_THEN [‘env3’,‘env'’,‘Var (Short "x")’,‘s3’,‘stpred’,‘dest’] strip_assume_tac) >>
      rfs[] >>
      ‘nsLookup env3.v (Short "sendloop") = 
       SOME (Recclosure env' (sendloop conf (MAP (CHR ∘ w2n) dest))
                 "sendloop")’
        by (qunabbrev_tac ‘env3’ >> qunabbrev_tac ‘env2’ >> rw[sendloop_def] >>
            EVAL_TAC >> rw[o_DEF]) >>
      ‘ck_equiv_hol env3 (LIST_TYPE WORD) (Var (Short "x")) (DROP conf.payload_size l)’
        by (irule ck_equiv_hol_Var >> qunabbrev_tac ‘env3’ >> EVAL_TAC >>
            qexists_tac ‘cVD’ >> rw[]) >>
      ‘stpred s3.ffi.ffi_state’
        by (qunabbrev_tac ‘s3’ >> qunabbrev_tac ‘s2’ >> fs[]) >>
      ‘ffi_accepts_rel stpred (valid_send_call_format conf dest) s3.ffi.oracle’
        by (qunabbrev_tac ‘s3’ >> qunabbrev_tac ‘s2’ >> fs[]) >>
      fs[] >>
      ntac 4 (first_x_assum (K ALL_TAC)) >>
      unite_nums "dc" >>
      rename [‘evaluate (s3 with clock := bc1) env3 [SND_EXP] =
                (s3 with <|clock := bc2; refs := s3.refs ++ drefsS; ffi:= _|>,
                 _)’] >>
      drule_then strip_assume_tac evaluate_add_to_clock >>
      fs[] >>
      Q.REFINE_EXISTS_TAC ‘bc1 + extra’ >>
      simp[state_component_equality,ffi_state_component_equality] >>
      ntac 2 (first_x_assum (K ALL_TAC)) >>
      rpt (qpat_x_assum ‘LIST_TYPE ^WORD8 _ _’ (K ALL_TAC)) >>
      rpt (qpat_x_assum ‘env_asm _ _’ (K ALL_TAC)) >>
      qunabbrev_tac ‘s3’ >> qunabbrev_tac ‘s2’ >> rw[]
      >- (rw [Once EQ_SYM_EQ,Once send_events_def,Once compile_message_def] >>
          PURE_ONCE_REWRITE_TAC [update_state_def] >>
          rw[MAP_ZIP] >>
          PURE_ONCE_REWRITE_TAC [send_events_def] >>
          simp[])
      >- (rw [Once EQ_SYM_EQ,Once send_events_def,
              Once compile_message_def,Once send_events_def]))
  >- (‘¬(LENGTH l ≤ conf.payload_size)’
        by (CCONTR_TAC >> fs eval_sl) >>
      ‘LENGTH l ≤ conf.payload_size’
        by (CCONTR_TAC >> fs eval_sl))
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

Theorem enc_ok_take:
  ∀conf cEnv x y vs.
    enc_ok conf cEnv (x ++ y) vs ⇒
    enc_ok conf cEnv x (TAKE (LENGTH x) vs) 
Proof
  Induct_on ‘x’ >> fs[enc_ok_def,LENGTH,TAKE] >>
  rw[] >> PURE_ONCE_REWRITE_TAC [enc_ok_def] >>
  ‘SUC (LENGTH x) ≤ LENGTH vs’
    by (‘∀a b. enc_ok conf cEnv a b ⇒ (LENGTH a = LENGTH b)’
          by (Induct_on ‘a’ >> Cases_on ‘b’ >>
              fs[enc_ok_def]) >>
        ‘LENGTH (h :: (x ++ y)) = LENGTH vs’
          by rw[] >>
        ‘SUC (LENGTH (x ++ y)) = LENGTH vs’
          by metis_tac[LENGTH] >>
        ‘LENGTH x ≤ LENGTH (x ++ y)’
          suffices_by (rw[] >>
                      ‘SUC (LENGTH x) ≤ SUC (LENGTH (x ++ y))’
                        by rw[] >>
                      simp[]) >>
        rw[]) >>
  Cases_on ‘vs’ >> fs[enc_ok_def] >>
  metis_tac[]
QED

Theorem enc_ok_drop:
  ∀conf cEnv x y vs.
    enc_ok conf cEnv (x ++ y) vs ⇒
    enc_ok conf cEnv y (DROP (LENGTH x) vs) 
Proof
  Induct_on ‘x’ >> fs[enc_ok_def,LENGTH,TAKE] >>
  rw[] >> PURE_ONCE_REWRITE_TAC [enc_ok_def] >>
  ‘SUC (LENGTH x) ≤ LENGTH vs’
    by (‘∀a b. enc_ok conf cEnv a b ⇒ (LENGTH a = LENGTH b)’
          by (Induct_on ‘a’ >> Cases_on ‘b’ >>
              fs[enc_ok_def]) >>
        ‘LENGTH (h :: (x ++ y)) = LENGTH vs’
          by rw[] >>
        ‘SUC (LENGTH (x ++ y)) = LENGTH vs’
          by metis_tac[LENGTH] >>
        ‘LENGTH x ≤ LENGTH (x ++ y)’
          suffices_by (rw[] >>
                      ‘SUC (LENGTH x) ≤ SUC (LENGTH (x ++ y))’
                        by rw[] >>
                      simp[]) >>
        rw[]) >>
  Cases_on ‘vs’ >> fs[enc_ok_def]
QED

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
                ⇒ ∃v'.  nsLookup (cEnv.v) (Short (ps2cs n)) = SOME v' ∧
                        ^(DATUM) v v'
End

(* CHECKING CONSISTENCY BETWEEN FFI AND PAYLOAD STATE *)
Definition ffi_state_cor_def:
  ffi_state_cor cpNum pSt (fNum,fQueue,fNet) ⇔
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
    conf.payload_size ≠ 0 ∧
    env_asm cEnv conf ∧
    enc_ok conf cEnv (letfuns pCd) vs ∧
    pSt_pCd_corr pSt pCd ∧
    sem_env_cor conf pSt cEnv ∧
    ffi_state_cor cpNum pSt cSt.ffi.ffi_state ∧
    cSt.ffi.oracle = (comms_ffi_oracle conf)
End

(* DEFINITION OF EQUIVALENT CAKEML EVALUTATIONS *)

Definition cEval_equiv_def:
  cEval_equiv conf (csA,crA) (csB,crB) ⇔
    ffi_eq conf csA.ffi.ffi_state csB.ffi.ffi_state ∧
    crA = crB ∧
    crA ≠ Rerr (Rabort Rtimeout_error)
End

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


Theorem send_events_is_stream:
  ∀conf l d.
    EVERY (valid_send_event_format conf l) (send_events conf l d)
Proof
  rw[] >> Cases_on ‘conf.payload_size = 0’
  >- rw[send_events_def,Once compile_message_def] >>
  completeInduct_on ‘LENGTH d’ >>
  rw[send_events_def,Once compile_message_def] >>
  rw[valid_send_event_format_def,valid_send_call_format_def,pad_def] >>
  ‘0 < LENGTH d’
    by (‘0 ≠ LENGTH d’
          suffices_by metis_tac[DECIDE “0 ≠ (n:num) ⇒ 0 < n”] >>
        CCONTR_TAC >> fs[] >>
        ‘final (pad conf d)’
          suffices_by fs[] >>
        simp[pad_def,final_def]) >>
  qmatch_goalsub_abbrev_tac ‘EVERY (valid_send_event_format conf l) func’ >>
  ‘func = send_events conf l (DROP conf.payload_size d)’
    suffices_by rw[] >>
  rw[Abbr ‘func’,send_events_def]
QED

Theorem ffi_state_cor_send_stream_irrel:
  ∀conf cpNum pSt ckFSt l send_stream P.
    ffi_state_cor cpNum pSt ckFSt ∧
    EVERY (valid_send_event_format conf l) send_stream ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_state_cor cpNum pSt (update_state ckFSt (comms_ffi_oracle conf) send_stream)
Proof
  Induct_on ‘send_stream’ >>
  rw[update_state_def] >>
  Cases_on ‘h’ >>
  PURE_ONCE_REWRITE_TAC [update_state_def] >>
  qmatch_goalsub_abbrev_tac ‘ffi_state_cor cpNum pSt (update_state ckFSt1 _ send_stream)’ >>
  rename1 ‘valid_send_event_format conf l (IO_event s l' d)’ >>
  ‘l' = l’
    by fs[valid_send_event_format_def,valid_send_call_format_def] >>
  fs[] >>
  first_x_assum (K ALL_TAC) >>
  last_x_assum irule >>
  qpat_assum ‘ffi_accepts_rel _ _ _’ (assume_tac o (REWRITE_RULE [ffi_accepts_rel_def])) >>
  first_x_assum (JSPECL_THEN [‘<|oracle := comms_ffi_oracle conf;
                               ffi_state := ckFSt;
                               io_events := ARB|>’,
                               ‘s’,‘l’,‘MAP FST d’]
                           strip_assume_tac) >>
  rfs[valid_send_event_format_def] >>
  fs[] >> qunabbrev_tac ‘ckFSt1’ >>
  qmatch_goalsub_rename_tac ‘ffi_state_cor _ _ ckFSt1’ >>
  rw[]
  >- (MAP_EVERY qexists_tac [‘P’,‘l’] >> fs[]) >>
  fs[ffi_accepts_rel_def,valid_send_event_format_def] >>
  rfs[] >>
  qpat_x_assum ‘∀a b c d. e’ (K ALL_TAC) >>
  fs[comms_ffi_oracle_def] >>
  ‘s = "send"’
    by fs[valid_send_call_format_def] >>
  fs[ffi_send_def] >> first_x_assum (K ALL_TAC) >>
  Cases_on ‘∃ns. strans conf ckFSt (ASend l (MAP SND d)) ns’ >>
  Cases_on ‘LENGTH d = SUC conf.payload_size’ >>
  fs[] >> rw[] >>
  irule SELECT_ELIM_THM >>
  rw[]
  >- (qpat_x_assum ‘strans _ _ _ ns’ (K ALL_TAC) >>
      qmatch_goalsub_rename_tac ‘ffi_state_cor _  _ ns’ >>
      Cases_on ‘ns’ >> Cases_on ‘ckFSt’ >>
      rename1 ‘strans conf (PN,R) _ (PN',R')’ >>
      ‘PN' = PN’
        by (drule strans_pres_pnum >>
            simp[]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘PN = cpNum’
        by (Cases_on ‘R’ >>
            fs[ffi_state_cor_def]) >>
      fs[] >>
      first_x_assum (K ALL_TAC) >>
      Cases_on ‘R’ >> Cases_on ‘R'’ >>
      rename1 ‘strans conf (_,Q,N) _ (_,Q',N')’ >>
      ‘isPREFIX Q Q'’
        suffices_by (rw[] >> fs[ffi_state_cor_def] >>
                     rw[] >> first_x_assum (qspec_then ‘extproc’ assume_tac) >>
                     qmatch_goalsub_abbrev_tac ‘isPREFIX (FILTER C pSt.queue) _’ >>
                     ‘isPREFIX (FILTER C Q) (FILTER C Q')’
                        suffices_by metis_tac[IS_PREFIX_TRANS] >>
                     rw[IS_PREFIX_FILTER]) >>
      metis_tac[strans_queue_pres])
  >- (qexists_tac ‘ns’ >> simp[])
QED

Theorem ffi_state_cor_send_events_irrel:
  ∀conf cpNum pSt ckFSt l d P.
    ffi_state_cor cpNum pSt ckFSt ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P ckFSt
    ⇒
    ffi_state_cor cpNum pSt (update_state ckFSt (comms_ffi_oracle conf)
                                          (send_events conf l d))
Proof
  rpt strip_tac >>
  ‘EVERY (valid_send_event_format conf l) (send_events conf l d)’
    suffices_by  (rw[] >> irule ffi_state_cor_send_stream_irrel >> rw[] >>
                  MAP_EVERY qexists_tac [‘P’,‘l’] >> rw[]) >>
  metis_tac[send_events_is_stream]
QED

Theorem ffi_eq_send_stream_irrel:
  ∀conf fs1 fs2 l send_stream P.
    ffi_eq conf fs1 fs2 ∧
    EVERY (valid_send_event_format conf l) send_stream ∧
    ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
    P fs1 ∧
    P fs2
    ⇒
    ffi_eq conf (update_state fs1 (comms_ffi_oracle conf) send_stream)
                (update_state fs2 (comms_ffi_oracle conf) send_stream)
Proof
  Induct_on ‘send_stream’ >>
  rw[update_state_def] >>
  Cases_on ‘h’ >>
  PURE_ONCE_REWRITE_TAC [update_state_def] >>
  qmatch_goalsub_abbrev_tac ‘ffi_eq conf (update_state fs1A _ _) (update_state fs2A _ _)’ >>
  last_x_assum irule >>
  ‘l' = l’
    by fs[valid_send_event_format_def,valid_send_call_format_def] >>
  fs[] >> first_x_assum (K ALL_TAC) >>
  qmatch_asmsub_rename_tac ‘IO_event s l data’ >> rw[]
  >- (MAP_EVERY qexists_tac [‘P’,‘l’] >> qunabbrev_tac ‘fs1A’ >>
      qunabbrev_tac ‘fs2A’ >> simp[] >>
      ‘∀si. P si ⇒ P (@st. comms_ffi_oracle conf s si l (MAP FST data) =
                            Oracle_return st (MAP SND data))’
        suffices_by rw[] >>
      rw[] >> SELECT_ELIM_TAC >> rw[] >>
      fs[ffi_accepts_rel_def] >>
      first_x_assum (JSPECL_THEN [‘<|oracle := comms_ffi_oracle conf;
                                     ffi_state := si;
                                     io_events := ARB|>’,
                                     ‘s’,‘l’,‘MAP FST data’]
                       strip_assume_tac) >>
      fs[valid_send_event_format_def] >>
      rfs[])
  >- (‘∃L. strans conf fs1 L fs1A ∧ strans conf fs2 L fs2A’
        suffices_by metis_tac[ffi_eq_pres] >>
      qexists_tac ‘ASend l (MAP FST data)’ >>
      qunabbrev_tac ‘fs1A’ >> qunabbrev_tac ‘fs2A’ >>
      ‘s = "send"’
        by fs[valid_send_event_format_def,valid_send_call_format_def] >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘LENGTH data = SUC conf.payload_size’
        by fs[valid_send_event_format_def,valid_send_call_format_def] >>
      rw[] >> qmatch_goalsub_rename_tac ‘strans conf si _ _’ >>
      SELECT_ELIM_TAC >> rw[] >>
      fs[ffi_accepts_rel_def,comms_ffi_oracle_def,ffi_send_def] >>
      first_x_assum (JSPECL_THEN [‘<|oracle := comms_ffi_oracle conf;
                                     ffi_state := si;
                                     io_events := ARB|>’,
                                     ‘"send"’,‘l’,‘MAP FST data’]
                       strip_assume_tac) >>
      fs[valid_send_event_format_def,valid_send_call_format_def,comms_ffi_oracle_def,ffi_send_def] >>
      rfs[] >>
      Cases_on ‘∃ns. strans conf si (ASend l (MAP SND data)) ns’ >> fs[] >>
      metis_tac[])
QED

Theorem ffi_eq_send_events_irrel:
∀conf fs1 fs2 l send_stream P d.
  ffi_eq conf fs1 fs2 ∧
  ffi_accepts_rel P (valid_send_call_format conf l) (comms_ffi_oracle conf) ∧
  P fs1 ∧
  P fs2 ⇒
  ffi_eq conf (update_state fs1 (comms_ffi_oracle conf) (send_events conf l d))
              (update_state fs2 (comms_ffi_oracle conf) (send_events conf l d))
Proof
  rpt strip_tac >>
  ‘EVERY (valid_send_event_format conf l) (send_events conf l d)’
    suffices_by  (rw[] >> irule ffi_eq_send_stream_irrel >> rw[] >>
                  MAP_EVERY qexists_tac [‘P’,‘l’] >> rw[]) >>
  metis_tac[send_events_is_stream]
QED


Theorem undo_encode_decode[simp]:
  ∀MEP:word8 list.
    MAP (λc. n2w (ORD c)) (EXPLODE (MAP (CHR ∘ w2n) MEP)) = MEP
Proof
  rw[] >> Induct_on ‘MEP’ >> rw[MAP,EXPLODE_def] >>
  ‘n2w o ORD o CHR o w2n = I’
    suffices_by metis_tac[o_DEF,I_THM] >>
  simp[n2w_ORD_CHR_w2n]
QED

Theorem w1ckV_is_1w:
  ∀env conf.
    env_asm env conf ⇒
    ck_equiv_hol env (LIST_TYPE ^WORD8) (w1ckV conf) [1w]
Proof
  rw[ck_equiv_hol_def,w1ckV_def] >>
  rw eval_sl >>
  fs[env_asm_def,has_v_def] >>
  rw trans_sl >>
  simp[list_type_num_def] >>
  MAP_EVERY qexists_tac [‘0’,‘0’,‘[]’] >>
  simp[state_component_equality]
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
  Induct_on ‘pCd’ >> rw[compile_endpoint_def]
  >- (rw (cEval_equiv_def::eval_sl_nf))
  >- (rw eval_sl_nf >>
      ‘∃ha_s. FLOOKUP pSt.bindings s = SOME ha_s’
        by fs[cpEval_valid_def,pSt_pCd_corr_def] >>
      ‘ck_equiv_hol cEnv NUM (App Opapp [Var conf.length; Var (Short (ps2cs s))]) (LENGTH ha_s)’
        by (irule ck_equiv_hol_App >>
            qexists_tac ‘LIST_TYPE ^WORD8’ >>
            rw[] >>irule ck_equiv_hol_Var
            >> fs[cpEval_valid_def,env_asm_def,has_v_def,sem_env_cor_def]) >>
      drule_then (JSPEC_THEN ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1 ‘∀dc.
                evaluate (cSt2 with clock := bc1_2 + dc) cEnv
                  [App Opapp [Var conf.length; Var (Short (ps2cs s))]] =
                (cSt2 with <|clock := dc + bc2_2; refs := cSt2.refs ++ drefs_2|>,
                 Rval [cV_2])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      drule_then (JSPEC_THEN ‘cSt1’ strip_assume_tac) ck_equiv_hol_apply >>
      rename1 ‘∀dc.
                evaluate (cSt1 with clock := bc1_1 + dc) cEnv
                  [App Opapp [Var conf.length; Var (Short (ps2cs s))]] =
                (cSt1 with <|clock := dc + bc2_1; refs := cSt1.refs ++ drefs_1|>,
                 Rval [cV_1])’ >>
      Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
      simp[] >>
      first_x_assum (K ALL_TAC) >>
      fs trans_sl >>
      ntac 3 (first_x_assum (K ALL_TAC)) >>
      unite_nums "dc1" >>
      unite_nums "dc2" >>
      (* BEGIN: DISPOSE REFS CHANGE *)
      qabbrev_tac ‘cSt1I = cSt1 with refs := (cSt1).refs ++ drefs_1’ >>
      qabbrev_tac ‘cSt2I = cSt2 with refs := (cSt2).refs ++ drefs_2’ >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1I’
        by (qunabbrev_tac ‘cSt1I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1’ (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2I’
        by (qunabbrev_tac ‘cSt2I’ >> fs[cpEval_valid_def]) >>
      qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2’ (K ALL_TAC) >>
      ‘ffi_eq conf (cSt1I).ffi.ffi_state (cSt2I).ffi.ffi_state’
        by simp[Abbr ‘cSt1I’, Abbr ‘cSt2I’] >>
      qpat_x_assum ‘ffi_eq conf (cSt1).ffi.ffi_state (cSt2).ffi.ffi_state’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt1A = cSt1 with refs := (cSt1).refs ++ drefs_1)’ (K ALL_TAC) >>
      qpat_x_assum ‘Abbrev (cSt2A = cSt2 with refs := (cSt2).refs ++ drefs_2)’ (K ALL_TAC) >>
      rename1 ‘ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state’ >>
      (* END: DISPOSE REFS CHANGE *)
      rw eval_sl_nf
      >- (last_x_assum (qspecl_then [‘conf’,‘cpNum’,‘cEnv’,
                                    ‘pSt’,‘vs’,‘cSt1’,‘cSt2’]
                                  assume_tac) >>
          rfs[cpEval_valid_def,letfuns_def] >>
          ‘pSt_pCd_corr pSt pCd’
            by fs[pSt_pCd_corr_def,Once pFv_def] >>
          fs[] >>
          qexists_tac ‘mc’ >>
          qspecl_then [‘conf’,‘cSt1’, ‘cSt2’, ‘cEnv’,
                       ‘[compile_endpoint conf vs pCd]’,
                       ‘mc’, ‘dc1’, ‘dc2’]
                      assume_tac clock_irrel >>
          rfs[] >>
          rw[])
      >- (fs[] >>
          ‘ALL_DISTINCT (MAP (λ(x,y,z). x) (sendloop conf (MAP (CHR ∘ w2n) l))) = T’
            by EVAL_TAC >>
          first_x_assum SUBST1_TAC >>
          rw eval_sl_nf >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ cEnvBR _’ >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ _ [App Opapp [_;Drop_Exp]]’ >>
          ‘ck_equiv_hol cEnvBR (LIST_TYPE ^WORD8) Drop_Exp (combin$C DROP ha_s n)’
              by (qunabbrev_tac ‘Drop_Exp’ >>
                  irule ck_equiv_hol_App >>
                  qexists_tac ‘NUM’ >>
                  rw[]
                  >- (irule ck_equiv_hol_Lit >>
                      rw trans_sl)
                  >- (irule ck_equiv_hol_App >>
                      qexists_tac ‘LIST_TYPE ^WORD8’ >>
                      rw[]
                      >- (irule ck_equiv_hol_Var >>
                          ‘nsLookup cEnvBR.v (Short (ps2cs s)) = nsLookup cEnv.v (Short (ps2cs s))’
                            by (qunabbrev_tac ‘cEnvBR’ >> rw[sendloop_def] >> EVAL_TAC) >>
                          first_x_assum SUBST1_TAC >>
                          fs[cpEval_valid_def,sem_env_cor_def])
                      >- (irule ck_equiv_hol_Var >>
                          ‘nsLookup cEnvBR.v conf.drop = nsLookup cEnv.v conf.drop’
                            by (qunabbrev_tac ‘cEnvBR’ >>
                                rw[sendloop_def] >> fs[cpEval_valid_def,env_asm_def,in_module_def]) >>
                          first_x_assum SUBST1_TAC >>    
                          fs[cpEval_valid_def,env_asm_def,has_v_def]))) >>
          JSPECL_THEN [‘conf’,‘combin$C DROP ha_s n’,‘cEnvBR’,‘cEnv’,‘Drop_Exp’,‘cSt1’,
                       ‘valid_send_dest l’,‘l’] strip_assume_tac sendloop_correct >>
          ‘env_asm cEnv conf’
            by fs[cpEval_valid_def] >>
          ‘conf.payload_size ≠ 0’
            by fs[cpEval_valid_def] >>
          ‘nsLookup cEnvBR.v (Short "sendloop")
            = SOME (Recclosure cEnv (sendloop conf (MAP (CHR o w2n) l)) "sendloop")’
            by rw[Abbr ‘cEnvBR’,sendloop_def,nsLookup_def,nsBind_def] >>
          qpat_x_assum ‘ck_equiv_hol _ _ Drop_Exp _’ assume_tac >>
          ‘ffi_accepts_rel (valid_send_dest l) (valid_send_call_format conf l) (cSt1.ffi.oracle)’
            by (‘cSt1.ffi.oracle = comms_ffi_oracle conf’
                  by fs[cpEval_valid_def] >>
                rw [send_invariant]) >>
          fs[] >>
          Cases_on ‘valid_send_dest l cSt1.ffi.ffi_state’
          >- (fs[] >> rename [‘evaluate (cSt1 with clock := bc1_1) cEnvBR _ =
                               (cSt1 with <|clock := bc2_1; refs := cSt1.refs ++ drefsS1;
                                            ffi := _|>,_)’] >>
              Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
              drule_then strip_assume_tac evaluate_add_to_clock >>
              fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
              qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
              ‘cSt1.ffi.oracle = cSt2.ffi.oracle’
                by fs[cpEval_valid_def] >>
              fs[] >> first_x_assum (K ALL_TAC) >>
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              JSPECL_THEN [‘conf’,‘combin$C DROP ha_s n’,‘cEnvBR’,‘cEnv’,‘Drop_Exp’,‘cSt2’,
                       ‘valid_send_dest l’,‘l’] strip_assume_tac sendloop_correct >>
              rfs[] >>
              ‘valid_send_dest l cSt2.ffi.ffi_state’
                by metis_tac[ffi_eq_sendval] >>
              fs[] >> rename [‘evaluate (cSt2 with clock := bc1_2) cEnvBR _ =
                               (cSt2 with <|clock := bc2_2; refs := cSt2.refs ++ drefsS2;
                                              ffi := _|>,_)’] >>
              Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
              drule_then strip_assume_tac evaluate_add_to_clock >>
              fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
              qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              simp[nsOptBind_def] >>
              qmatch_goalsub_abbrev_tac ‘∃mc. cEval_equiv conf
                                        (evaluate (cSt1M with clock := dc1 + mc) cEnv _)
                                        (evaluate (cSt2M with clock := dc2 + mc) cEnv _)’ >>
              last_x_assum (JSPECL_THEN [‘conf’,‘cpNum’,‘cEnv’,‘pSt’,‘vs’,
                                         ‘cSt1M’,‘cSt2M’] strip_assume_tac) >>
              ‘cpEval_valid conf cpNum cEnv pSt pCd vs cSt1M’
                by (qunabbrev_tac ‘cSt1M’ >> rw[cpEval_valid_def] >>
                    fs[cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def] >>
                    irule ffi_state_cor_send_events_irrel >> rfs[] >>
                    qexists_tac ‘valid_send_dest l’ >> fs[]) >>
              ‘cpEval_valid conf cpNum cEnv pSt pCd vs cSt2M’
                by (qunabbrev_tac ‘cSt2M’ >> rw[cpEval_valid_def] >>
                    fs[cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def] >>
                    irule ffi_state_cor_send_events_irrel >> rfs[] >>
                    qexists_tac ‘valid_send_dest l’ >> fs[]) >>
              ‘ffi_eq conf cSt1M.ffi.ffi_state cSt2M.ffi.ffi_state’
                suffices_by (rw[] >> fs[] >> metis_tac[clock_irrel]) >>
              qunabbrev_tac ‘cSt1M’ >> qunabbrev_tac ‘cSt2M’ >> simp[] >>
              qpat_x_assum ‘ffi_accepts_rel _ _ _’ assume_tac >>
              qpat_x_assum ‘ffi_eq conf _ _’ assume_tac >>
              ‘cSt2.ffi.oracle = comms_ffi_oracle conf’
                by fs[cpEval_valid_def] >>
              fs[] >>
              first_x_assum (K ALL_TAC) >>
              qpat_x_assum ‘valid_send_dest _ cSt1.ffi.ffi_state’ assume_tac >>
              qpat_x_assum ‘valid_send_dest _ cSt2.ffi.ffi_state’ assume_tac >>
              ntac 13 (last_x_assum (K ALL_TAC)) >>
              qabbrev_tac ‘fs1 = cSt1.ffi.ffi_state’ >>
              qabbrev_tac ‘fs2 = cSt2.ffi.ffi_state’ >>
              ntac 2 (first_x_assum (K ALL_TAC)) >>
              irule ffi_eq_send_events_irrel >> simp[] >>
              qexists_tac ‘valid_send_dest l’ >> simp[])
          >- (qpat_x_assum ‘valid_send_dest _ _ ⇒ _’ (K ALL_TAC) >>
              rw eval_sl >>
              drule_then (JSPEC_THEN ‘cSt1’ strip_assume_tac) ck_equiv_hol_apply >>
              rename [‘∀dc. evaluate (cSt1 with clock := bc1_1 + dc) cEnvBR _ =
                               (cSt1 with <|clock := dc + bc2_1; refs := cSt1.refs ++ drefsD1|>,
                                Rval [cVD1])’] >>
              Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
              simp[] >>
              first_x_assum (K ALL_TAC) >>
              Q.REFINE_EXISTS_TAC ‘SUC mc’ >>
              rw[ADD1,dec_clock_def] >> 
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              drule_then (JSPEC_THEN ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
              rename [‘∀dc. evaluate (cSt2 with clock := bc1_2 + dc) cEnvBR _ =
                               (cSt2 with <|clock := dc + bc2_2; refs := cSt2.refs ++ drefsD2|>,
                                Rval [cVD2])’] >>
              Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
              simp[] >>
              first_x_assum (K ALL_TAC) >>
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              rw (sendloop_def::do_opapp_def::eval_sl) >>
              PURE_ONCE_REWRITE_TAC [find_recfun_def] >>
              rw [GSYM sendloop_def] >>
              PURE_ONCE_REWRITE_TAC eval_sl_nf >>
              (* BEGIN: DISPOSE REFS CHANGE *)
              qabbrev_tac ‘cSt1I = cSt1 with refs := (cSt1).refs ++ drefsD1’ >>
              qabbrev_tac ‘cSt2I = cSt2 with refs := (cSt2).refs ++ drefsD2’ >>
              ‘¬valid_send_dest l cSt1I.ffi.ffi_state’
                by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
              qpat_x_assum ‘¬valid_send_dest l cSt1.ffi.ffi_state’ (K ALL_TAC) >>
              ‘cSt1.ffi.oracle = cSt1I.ffi.oracle’
                by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
              fs[] >>
              first_x_assum (K ALL_TAC) >>
              ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1I’
                by (qunabbrev_tac ‘cSt1I’ >> fs[cpEval_valid_def]) >>
              qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1’ (K ALL_TAC) >>
              ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2I’
                by (qunabbrev_tac ‘cSt2I’ >> fs[cpEval_valid_def]) >>
              qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2’ (K ALL_TAC) >>
              ‘ffi_eq conf (cSt1I).ffi.ffi_state (cSt2I).ffi.ffi_state’
                by simp[Abbr ‘cSt1I’, Abbr ‘cSt2I’] >>
              qpat_x_assum ‘ffi_eq conf (cSt1).ffi.ffi_state (cSt2).ffi.ffi_state’ (K ALL_TAC) >>
              qpat_x_assum ‘Abbrev (cSt1A = cSt1 with refs := (cSt1).refs ++ drefsD1)’ (K ALL_TAC) >>
              qpat_x_assum ‘Abbrev (cSt2A = cSt2 with refs := (cSt2).refs ++ drefsD2)’ (K ALL_TAC) >>
              rename1 ‘ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state’ >>
              (* END: DISPOSE REFS CHANGE *)
              (* Evaluate padv *)
              qmatch_goalsub_abbrev_tac ‘evaluate (cSt1 with clock := _) cEnvAT1 _’ >>
              qmatch_goalsub_abbrev_tac ‘evaluate (cSt2 with clock := _) cEnvAT2 _’ >>
              JSPECL_THEN [‘cEnvAT1’, ‘conf’, ‘DROP n ha_s’, ‘cVD1’,‘Var (Short "x")’,
                           ‘cSt1’,‘cSt1’,‘[]’] strip_assume_tac padv_correct >>
              ‘env_asm cEnvAT1 conf’
                by fs[Abbr ‘cEnvAT1’,env_asm_def,in_module_def,has_v_def] >>
              fs[] >> first_x_assum (K ALL_TAC) >> rfs[] >>
              ‘evaluate cSt1 cEnvAT1 [Var (Short "x")] = (cSt1 with refs := cSt1.refs, Rval [cVD1])’
                by (qunabbrev_tac ‘cEnvAT1’ >> rw ([nsLookup_def,nsBind_def,nsOptBind_def]@eval_sl) >>
                    simp[state_component_equality]) >>
              fs[] >> first_x_assum (K ALL_TAC) >>
              rename1 ‘evaluate (cSt1 with clock := bc1_1) _ [_] =
                        (cSt1 with <|clock:=bc2_1;refs:=cSt1.refs++drefs_1|>,Rval[Loc num1])’ >>
              Q.REFINE_EXISTS_TAC ‘bc1_1 + mc’ >>
              drule_then strip_assume_tac evaluate_add_to_clock >>
              fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
              qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              JSPECL_THEN [‘cEnvAT2’, ‘conf’, ‘DROP n ha_s’, ‘cVD2’,‘Var (Short "x")’,
                           ‘cSt2’,‘cSt2’,‘[]’] strip_assume_tac padv_correct >>
              ‘env_asm cEnvAT2 conf’
                by fs[Abbr ‘cEnvAT2’,env_asm_def,in_module_def,has_v_def] >>
              fs[] >> first_x_assum (K ALL_TAC) >> rfs[] >>
              ‘evaluate cSt2 cEnvAT2 [Var (Short "x")] = (cSt2 with refs := cSt2.refs, Rval [cVD2])’
                by (qunabbrev_tac ‘cEnvAT2’ >> rw ([nsLookup_def,nsBind_def,nsOptBind_def]@eval_sl) >>
                    simp[state_component_equality]) >>
              fs[] >> first_x_assum (K ALL_TAC) >>
              rename1 ‘evaluate (cSt2 with clock := bc1_2) _ [_] =
                        (cSt2 with <|clock:=bc2_2;refs:=cSt2.refs++drefs_2|>,Rval[Loc num2])’ >>
              Q.REFINE_EXISTS_TAC ‘bc1_2 + mc’ >>
              drule_then strip_assume_tac evaluate_add_to_clock >>
              fs[] >> simp[] >> qpat_x_assum ‘evaluate _ _ _ = _’ (K ALL_TAC) >>
              qpat_x_assum ‘∀extra. evaluate _ _ _ = _’ (K ALL_TAC) >>
              unite_nums "dc1" >>
              unite_nums "dc2" >>
              (* Done padv *)
              (* BEGIN: DISPOSE REFS CHANGE *)
              qabbrev_tac ‘cSt1I = cSt1 with refs := (cSt1).refs ++ drefs_1’ >>
              qabbrev_tac ‘cSt2I = cSt2 with refs := (cSt2).refs ++ drefs_2’ >>
              ‘¬valid_send_dest l cSt1I.ffi.ffi_state’
                by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
              qpat_x_assum ‘¬valid_send_dest l cSt1.ffi.ffi_state’ (K ALL_TAC) >>
              ‘cSt1.ffi.oracle = cSt1I.ffi.oracle’
                by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
              fs[] >> first_x_assum (K ALL_TAC) >>
              ‘cSt1.refs ++ drefs_1  = cSt1I.refs’
                by (qunabbrev_tac ‘cSt1I’ >> simp[]) >>
              fs[] >> first_x_assum (K ALL_TAC) >>
              ‘cSt2.refs ++ drefs_2  = cSt2I.refs’
                by (qunabbrev_tac ‘cSt2I’ >> simp[]) >>
              fs[] >> first_x_assum (K ALL_TAC) >>
              ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1I’
                by (qunabbrev_tac ‘cSt1I’ >> fs[cpEval_valid_def]) >>
              qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt1’ (K ALL_TAC) >>
              ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2I’
                by (qunabbrev_tac ‘cSt2I’ >> fs[cpEval_valid_def]) >>
              qpat_x_assum ‘cpEval_valid conf cpNum cEnv pSt (Send l s n pCd) vs cSt2’ (K ALL_TAC) >>
              ‘ffi_eq conf (cSt1I).ffi.ffi_state (cSt2I).ffi.ffi_state’
                by simp[Abbr ‘cSt1I’, Abbr ‘cSt2I’] >>
              qpat_x_assum ‘ffi_eq conf (cSt1).ffi.ffi_state (cSt2).ffi.ffi_state’ (K ALL_TAC) >>
              qpat_x_assum ‘Abbrev (cSt1I = cSt1 with refs := cSt1I.refs)’ (K ALL_TAC) >>
              qpat_x_assum ‘Abbrev (cSt2I = cSt2 with refs := cSt2I.refs)’ (K ALL_TAC) >>
              rename1 ‘ffi_eq conf cSt1.ffi.ffi_state cSt2.ffi.ffi_state’ >>
              (* END: DISPOSE REFS CHANGE *)
              PURE_ONCE_REWRITE_TAC eval_sl_nf >>
              qmatch_goalsub_abbrev_tac ‘evaluate (cSt1 with clock := _) cEnvFF1 [App (FFI "send")[d1;v1]]’ >>
              ‘∀mc. evaluate (cSt1 with clock := mc) cEnvFF1 [App (FFI "send") [d1;v1]] = 
                (cSt1 with clock := mc,
                 Rerr (Rabort (Rffi_error (Final_event "send" l (pad conf (DROP n ha_s)) FFI_diverged))))’
                by (rw([Abbr ‘cEnvFF1’,Abbr ‘v1’,Abbr ‘d1’,nsLookup_def,nsBind_def,
                        nsOptBind_def]@eval_sl)
                    >- (fs[store_lookup_def] >> rw[] >>
                        ‘cSt1.ffi.oracle = comms_ffi_oracle conf’
                          by fs[cpEval_valid_def] >> rw[comms_ffi_oracle_def,ffi_send_def]
                        >- (‘LENGTH (pad conf (DROP n ha_s)) = SUC conf.payload_size’
                              suffices_by fs[] >>
                            first_x_assum (K ALL_TAC) >> rw[pad_def])
                        >- (‘valid_send_dest l cSt1.ffi.ffi_state’
                              suffices_by fs[] >>
                            metis_tac[strans_dest_check])
                        >- (simp [state_component_equality]))
                    >- (qmatch_asmsub_abbrev_tac ‘store_lookup N cSt1.refs = SOME SV’ >>
                        ‘store_lookup N cSt1.refs = NONE’
                          suffices_by fs[] >>
                        rpt (qpat_x_assum ‘store_lookup _ _ = _’ (K ALL_TAC)) >>
                        rw[store_lookup_def])) >>
              simp[] >> first_x_assum (K ALL_TAC) >>
              ‘¬valid_send_dest l cSt2.ffi.ffi_state’
                by metis_tac[ffi_eq_sendval] >>
              qmatch_goalsub_abbrev_tac ‘evaluate (cSt2 with clock := _) cEnvFF2 [App (FFI "send")[d1;v1]]’ >>
              ‘∀mc. evaluate (cSt2 with clock := mc) cEnvFF2 [App (FFI "send") [d1;v1]] = 
                (cSt2 with clock := mc,
                 Rerr (Rabort (Rffi_error (Final_event "send" l (pad conf (DROP n ha_s)) FFI_diverged))))’
                by (rw([Abbr ‘cEnvFF2’,Abbr ‘v1’,Abbr ‘d1’,nsLookup_def,nsBind_def,
                        nsOptBind_def]@eval_sl)
                    >- (fs[store_lookup_def] >> rw[] >>
                        ‘cSt2.ffi.oracle = comms_ffi_oracle conf’
                          by fs[cpEval_valid_def] >> rw[comms_ffi_oracle_def,ffi_send_def]
                        >- (‘LENGTH (pad conf (DROP n ha_s)) = SUC conf.payload_size’
                              suffices_by fs[] >>
                            first_x_assum (K ALL_TAC) >> rw[pad_def])
                        >- (‘valid_send_dest l cSt2.ffi.ffi_state’
                              suffices_by fs[] >>
                            metis_tac[strans_dest_check])
                        >- (simp[state_component_equality]))
                    >- (qmatch_asmsub_abbrev_tac ‘store_lookup N cSt2.refs = SOME SV’ >>
                        ‘store_lookup N cSt2.refs = NONE’
                          suffices_by fs[] >>
                        rpt (qpat_x_assum ‘store_lookup _ _ = _’ (K ALL_TAC)) >>
                        rw[store_lookup_def])) >>
              simp[] >> first_x_assum (K ALL_TAC) >>
              rw[cEval_equiv_def])
          )
      >- (rw[cEval_equiv_def]))     
  >- (cheat)
  >- (‘∃ha_s. FLOOKUP pSt.bindings s = SOME ha_s’
        by fs[cpEval_valid_def,pSt_pCd_corr_def] >>
      ‘ck_equiv_hol cEnv (LIST_TYPE ^WORD8) (Var (Short (ps2cs s))) ha_s’
        by (irule ck_equiv_hol_Var >> fs[cpEval_valid_def,sem_env_cor_def]) >>
      ‘ck_equiv_hol cEnv (LIST_TYPE ^WORD8) (w1ckV conf) [1w]’
        by (irule w1ckV_is_1w >> fs[cpEval_valid_def]) >>
      qmatch_goalsub_abbrev_tac ‘evaluate (cSt1 with clock := _) _ [If Eexp _ _]’ >>
      ‘ck_equiv_hol cEnv BOOL Eexp (ha_s = [1w])’
        by (qunabbrev_tac ‘Eexp’ >> irule ck_equiv_hol_apply_list_word8_equality >>
            fs[]) >>
      rw eval_sl >>
      drule_then (JSPEC_THEN ‘cSt1’ strip_assume_tac) ck_equiv_hol_apply >>
      Q.REFINE_EXISTS_TAC ‘bc1 + mc’ >>
      simp[] >>
      qpat_x_assum ‘∀dc. evaluate _ _ _ = _’ (K ALL_TAC) >>
      qmatch_goalsub_rename_tac ‘evaluate (cSt2 with clock := dcA + _) _ [_]’ >>
      drule_then (JSPEC_THEN ‘cSt2’ strip_assume_tac) ck_equiv_hol_apply >>
      Q.REFINE_EXISTS_TAC ‘bc1 + mc’ >>
      simp[] >>
      qpat_x_assum ‘∀dc. evaluate _ _ _ = _’ (K ALL_TAC) >>
      unite_nums "dc1" >> unite_nums "dc2" >>
      Cases_on ‘ha_s = [1w]’ >>
      fs [BOOL_def] >> rw eval_sl >>
      qmatch_goalsub_abbrev_tac
      ‘∃mc.
        cEval_equiv conf
          (evaluate
            (cSt1A with clock := dc1 + mc) cEnv
            [compile_endpoint conf nvs pCdG])
          (evaluate
            (cSt2A with clock := dc2 + mc) cEnv
            [compile_endpoint conf nvs pCdG])’ >>
      qpat_x_assum ‘∀conf cpNum cEnv pSt vs cSt1 cSt1.
                      cpEval_valid _ _ _ _ pCdG _ _ ∧ _ ⇒
                      ∃mc. _’
                  (JSPECL_THEN [‘conf’,‘cpNum’,‘cEnv’,‘pSt’,
                                ‘nvs’,‘cSt1A’,‘cSt2A’]
                                strip_assume_tac) >>
      ‘ffi_eq conf cSt1A.ffi.ffi_state cSt2A.ffi.ffi_state’
        by simp[Abbr ‘cSt1A’,Abbr ‘cSt2A’] >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘cpEval_valid conf cpNum cEnv pSt pCdG nvs cSt1A’
        by (fs[Abbr ‘cSt1A’,cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def] >>
            qunabbrev_tac ‘nvs’ >>
            qpat_x_assum ‘enc_ok conf cEnv _ _’ assume_tac >>
            ntac 18 (last_x_assum (K ALL_TAC)) >>
            metis_tac[enc_ok_drop,enc_ok_take]) >>
      ‘cpEval_valid conf cpNum cEnv pSt pCdG nvs cSt2A’
        by fs[Abbr ‘cSt2A’,cpEval_valid_def,letfuns_def,pSt_pCd_corr_def,pFv_def] >>
      fs[] >> ntac 2 (first_x_assum (K ALL_TAC)) >>
      qexists_tac ‘mc’ >> irule clock_irrel >> fs[])
  >- (cheat)
QED
val _ = export_theory ();