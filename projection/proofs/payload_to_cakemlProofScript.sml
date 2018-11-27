open preamble payloadLangTheory payload_to_cakemlTheory
     evaluateTheory terminationTheory ml_translatorTheory evaluatePropsTheory
     semanticPrimitivesTheory;

val _ = new_theory "payload_to_cakemlProof";

val has_v_def = Define
  `has_v env n cfty f =
   (?v. nsLookup env n = SOME v
        /\ cfty f v)
  `

val WORD8 = ``WORD:word8 -> v -> bool``

val in_module_def = Define `
  in_module name =
  !x y (env:(modN,varN,v) namespace). nsLookup (nsBind x y env) name = nsLookup env name
  `;

val env_asm_def = Define `
  env_asm env conf = (
    has_v env.v conf.length (LIST_TYPE ^WORD8 --> NUM) LENGTH /\
    has_v env.v conf.null (LIST_TYPE ^WORD8 --> BOOL) NULL /\
    has_v env.v conf.take (LIST_TYPE ^WORD8 --> NUM --> LIST_TYPE ^WORD8) (combin$C TAKE) /\
    has_v env.v conf.drop (LIST_TYPE ^WORD8 --> NUM --> LIST_TYPE ^WORD8) (combin$C DROP) /\
    (?v. nsLookup env.v conf.fromList = SOME v /\
         (!l lv.
           LIST_TYPE ^WORD8 l lv
           ==> !s1: unit semanticPrimitives$state. ?env' exp ck1 ck2. do_opapp [v; lv] = SOME(env',exp)
               /\ evaluate (s1 with clock := ck1) env' [exp] =
                  (s1 with <|clock := ck2; refs := s1.refs ++ [W8array l]|>,Rval [Loc(LENGTH s1.refs)]))) /\
    in_module conf.length /\
    in_module conf.null /\
    in_module conf.take /\
    in_module conf.drop /\
    in_module conf.fromList)
  `;


val evaluate_empty_state_norel = Q.prove(
  `∀s x refs refs' exp env ck1 ck2.
    evaluate (empty_state with <|clock := ck1; refs := refs|>) env [exp] =
             (empty_state with <|clock := ck2; refs := refs ++ refs'|>,Rval [x]) ⇒
    ∃ck1 ck2.
      evaluate (s with <|clock := ck1; refs := refs; ffi:= s.ffi|>) env [exp] =
      (s with <|clock := ck2; refs := refs ++ refs'; ffi:= s.ffi|>,Rval [x])`,
  rpt strip_tac >>
  qabbrev_tac `a1 = s with refs := refs` >>
  `refs = a1.refs` by(qunabbrev_tac `a1` >> simp[]) >>
  fs[] >>
  drule (SIMP_RULE (srw_ss()) [ml_progTheory.eval_rel_def,PULL_EXISTS] evaluate_empty_state_IMP
         |> GEN_ALL) >>
  unabbrev_all_tac >>
  Cases_on `s` >> fs[state_fn_updates]);

val LUPDATE_REPLICATE = Q.store_thm("LUPDATE_REPLICATE",
  `!n m x y. n < m ==>
   LUPDATE x n (REPLICATE m y) = REPLICATE n y ++ [x] ++ REPLICATE (m - (n + 1)) y`,
  Induct >> Cases >> rw[LUPDATE_def] >> simp[ADD1]);

val padv_correct = Q.store_thm("padv_correct",`
  !env conf l lv le s0 s1 s2 refs.
  env_asm env conf /\
  LIST_TYPE ^WORD8 l lv /\
  evaluate$evaluate s1 env [le] = (s2 with refs := s1.refs ++ refs, Rval [lv])
  ==>
  ?ck1 ck2 refs' num lv'.
  evaluate$evaluate (s1 with clock:= ck1) env [App Opapp [padv conf; le]] =
           (s2 with <|clock := ck2; refs := APPEND s1.refs refs'|>, Rval [Loc num]) /\
  store_lookup num (APPEND s1.refs refs') = SOME(W8array(pad conf l))
  `,
  rpt strip_tac >>
  drule evaluate_add_to_clock >>
  simp[] >>
  qabbrev_tac `ack = s2.clock` >>
  fs[env_asm_def,in_module_def,has_v_def] >>
  strip_tac >>
  Q.REFINE_EXISTS_TAC `extra + s1.clock` >>
  simp[Once evaluate_def] >>
  simp[padv_def,do_opapp_def,buffer_size_def,payload_size_def] >>
  Q.REFINE_EXISTS_TAC `extra + 1` >>
  simp[Once evaluate_def] >>
  simp[dec_clock_def,do_app_def,store_alloc_def,ml_progTheory.nsLookup_nsBind_compute,
       namespaceTheory.nsOptBind_def] >>
  ntac 6 (simp[Once evaluate_def]) >>
  simp[dec_clock_def,do_app_def,store_alloc_def,ml_progTheory.nsLookup_nsBind_compute,
       namespaceTheory.nsOptBind_def] >>
  ntac 6 (simp[Once evaluate_def]) >>
  simp[ml_progTheory.nsLookup_nsBind_compute] >>
  ntac 2 (simp[Once evaluate_def]) >>
  qpat_assum `(LIST_TYPE ^WORD8 --> NUM) LENGTH _` (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
  simp[] >> disch_then drule >>
  qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>
  disch_then(qspec_then `a1` strip_assume_tac) >>
  qunabbrev_tac `a1` >>
  Q.REFINE_EXISTS_TAC `extra + 1` >>
  simp[dec_clock_def] >>
  Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `clock_fupd (K ack1)` >>
  Q.REFINE_EXISTS_TAC `extra + ack1` >>
  drule evaluate_add_to_clock >>
  simp[SimpL ``$==>``] >>
  disch_then(qspec_then `ack` mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >>
  disch_then kall_tac >>
  fs[NUM_def,INT_def] >>  
  simp[do_app_def] >>
  simp[terminationTheory.do_eq_def,lit_same_type_def,Boolv_def,do_if_def] >>
  PURE_REWRITE_TAC [ADD_ASSOC] >>
  qpat_abbrev_tac `ack2 = ack + _` >> pop_assum kall_tac >>
  Cases_on `LENGTH l = conf.payload_size` >-
    (ntac 7 (simp[Once evaluate_def]) >>
     simp[do_app_def,store_lookup_def,EL_APPEND_EQN,store_assign_def,
          store_v_same_type_def,ml_progTheory.nsLookup_nsBind_compute,
          namespaceTheory.nsOptBind_def,lupdate_append2] >>
     ntac 10 (simp[Once evaluate_def]) >>
     qpat_assum `(LIST_TYPE WORD --> NUM --> LIST_TYPE WORD) (combin$C TAKE) _` (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
     simp[] >> disch_then drule >>
     qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>     
     disch_then(qspec_then `a1` strip_assume_tac) >>
     qunabbrev_tac `a1` >>
     Q.REFINE_EXISTS_TAC `extra + 1` >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac `clock_fupd (K ack3)` >>
     Q.REFINE_EXISTS_TAC `extra + ack3` >>
     drule evaluate_add_to_clock >>
     simp[SimpL ``$==>``] >>
     disch_then(qspec_then `ack2` mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     first_x_assum(qspecl_then [`conf.payload_size`,`Litv (IntLit (&conf.payload_size))`] mp_tac) >>
     impl_tac >- simp[NUM_def,INT_def] >>
     qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>
     disch_then(qspec_then `a1` strip_assume_tac) >>
     qunabbrev_tac `a1` >>
     Q.REFINE_EXISTS_TAC `extra + 1` >>
     simp[dec_clock_def] >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack4 = ack2 + _` >> pop_assum kall_tac >>
     Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac `clock_fupd (K ack5)` >>
     Q.REFINE_EXISTS_TAC `extra + ack5` >>
     drule evaluate_add_to_clock >>
     simp[SimpL ``$==>``] >>
     disch_then(qspec_then `ack4` mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >>
     disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack6 = ack4 + _` >> pop_assum kall_tac >>
     simp[Once evaluate_def] >>
     last_x_assum drule >>
     qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>
     disch_then(qspec_then `empty_state with refs := a1` mp_tac) >>
     simp[] >>
     qunabbrev_tac `a1` >> strip_tac >>
     Q.REFINE_EXISTS_TAC `extra + 1` >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac `clock_fupd (K ack7)` >>
     Q.REFINE_EXISTS_TAC `extra + ack7` >>
     drule evaluate_add_to_clock >>
     simp[SimpL ``$==>``] >>
     disch_then(qspec_then `ack6` mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack8 = ack6 + _` >> pop_assum kall_tac >>
     simp[evaluate_def,namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute,
          do_app_def,store_lookup_def,EL_APPEND_EQN,copy_array_def,integerTheory.INT_ABS,
          LUPDATE_APPEND,LUPDATE_def] >>
     qmatch_goalsub_abbrev_tac `lhs < rhs` >>
    `rhs = lhs`
     by (unabbrev_all_tac >>
         rw[] >- intLib.COOPER_TAC >>
         simp[GSYM (PURE_REWRITE_RULE [Once integerTheory.INT_ADD_SYM,integerTheory.INT_1]
                                      integerTheory.int_of_num)]) >>
     simp[] >>    
     MAP_EVERY qunabbrev_tac [`lhs`,`rhs`] >>
     simp[store_assign_def,store_v_same_type_def,EL_APPEND_EQN,
          semanticPrimitivesTheory.state_component_equality,LUPDATE_APPEND,
          LUPDATE_def] >>
     simp[TAKE_TAKE,pad_def] >>
     simp[DROP_LENGTH_TOO_LONG,LENGTH_LUPDATE] >>
     simp[REWRITE_RULE [ADD1] REPLICATE,LUPDATE_def] >>
     simp[TAKE_LENGTH_TOO_LONG]) >>
  rpt(qpat_x_assum `do_opapp _ = _` kall_tac) >>
  ntac 8 (simp[Once evaluate_def]) >>
  qpat_assum `(LIST_TYPE ^WORD8 --> NUM) LENGTH _` (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
  simp[] >> disch_then drule >>
  qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>
  disch_then(qspec_then `a1` strip_assume_tac) >>
  qunabbrev_tac `a1` >>
  Q.REFINE_EXISTS_TAC `extra + 1` >>
  simp[dec_clock_def] >>
  Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `clock_fupd (K ack3)` >>
  Q.REFINE_EXISTS_TAC `extra + ack3` >>
  drule evaluate_add_to_clock >>
  simp[SimpL ``$==>``] >>
  disch_then(qspec_then `ack2` mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >>
  disch_then kall_tac >>
  fs[NUM_def,INT_def] >>  
  simp[do_app_def] >>
  simp[semanticPrimitivesTheory.opb_lookup_def,lit_same_type_def,Boolv_def,do_if_def] >>
  Cases_on `LENGTH l < conf.payload_size` >-
    (simp[] >>
     ntac 7 (simp[Once evaluate_def]) >>
     simp[do_app_def,store_lookup_def,EL_APPEND_EQN,store_assign_def,
          store_v_same_type_def,ml_progTheory.nsLookup_nsBind_compute,
          namespaceTheory.nsOptBind_def,lupdate_append2] >>
     ntac 5 (simp[Once evaluate_def]) >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack4 = ack2 + _` >> pop_assum kall_tac >>    
     last_x_assum drule >>
     qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>
     disch_then(qspec_then `empty_state with refs := a1` mp_tac) >>
     simp[] >>
     qunabbrev_tac `a1` >> strip_tac >>
     Q.REFINE_EXISTS_TAC `extra + 1` >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac `clock_fupd (K ack5)` >>
     Q.REFINE_EXISTS_TAC `extra + ack5` >>
     drule evaluate_add_to_clock >>
     simp[SimpL ``$==>``] >>
     disch_then(qspec_then `ack4` mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack6 = ack4 + _` >> pop_assum kall_tac >>
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
     `Num (1 + (&conf.payload_size − &LENGTH l)) = 1 + (conf.payload_size - LENGTH l)`
       by(intLib.COOPER_TAC) >>
     `Num (&conf.payload_size − &LENGTH l) = conf.payload_size - LENGTH l`
       by(intLib.COOPER_TAC) >>
     simp[] >>
     simp[REWRITE_RULE [ADD1] REPLICATE,LUPDATE_APPEND,REWRITE_RULE [ADD1] LUPDATE_def] >>
     `conf.payload_size − LENGTH l = conf.payload_size − (LENGTH l + 1) + 1`
       by(intLib.COOPER_TAC) >>
     pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
     PURE_REWRITE_TAC[REWRITE_RULE [ADD1] LUPDATE_def] >>
     simp[TAKE_cons] >>     
     IF_CASES_TAC >- (
        spose_not_then kall_tac >>
        pop_assum mp_tac >> intLib.COOPER_TAC) >>
     `Num (1 + (&conf.payload_size − &LENGTH l) + &LENGTH l) = conf.payload_size + 1`
       by(intLib.COOPER_TAC) >>
     simp[DROP_LENGTH_TOO_LONG,LENGTH_LUPDATE,LENGTH_REPLICATE] >>
     simp[LUPDATE_REPLICATE,TAKE_APPEND] >>
     simp[TAKE_LENGTH_TOO_LONG,LENGTH_REPLICATE] >>
     simp[pad_def]) >>
    (simp[] >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack4 = ack2 + _` >> pop_assum kall_tac >>
     ntac 7 (simp[Once evaluate_def]) >>
     simp[do_app_def,store_lookup_def,EL_APPEND_EQN,store_assign_def,
          store_v_same_type_def,ml_progTheory.nsLookup_nsBind_compute,
          namespaceTheory.nsOptBind_def,lupdate_append2] >>
     ntac 10 (simp[Once evaluate_def]) >>
     qpat_assum `(LIST_TYPE WORD --> NUM --> LIST_TYPE WORD) (combin$C TAKE) _` (mp_tac o REWRITE_RULE[ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,ml_progTheory.eval_rel_def]) >>
     simp[] >> disch_then drule >>
     qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>     
     disch_then(qspec_then `a1` strip_assume_tac) >>
     qunabbrev_tac `a1` >>
     Q.REFINE_EXISTS_TAC `extra + 1` >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac `clock_fupd (K ack5)` >>
     Q.REFINE_EXISTS_TAC `extra + ack5` >>
     drule evaluate_add_to_clock >>
     simp[SimpL ``$==>``] >>
     disch_then(qspec_then `ack4` mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     first_x_assum(qspecl_then [`conf.payload_size`,`Litv (IntLit (&conf.payload_size))`] mp_tac) >>
     impl_tac >- simp[NUM_def,INT_def] >>
     qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>
     disch_then(qspec_then `a1` strip_assume_tac) >>
     qunabbrev_tac `a1` >>
     Q.REFINE_EXISTS_TAC `extra + 1` >>
     simp[dec_clock_def] >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack6 = ack4 + _` >> pop_assum kall_tac >>
     Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac `clock_fupd (K ack7)` >>
     Q.REFINE_EXISTS_TAC `extra + ack7` >>
     drule evaluate_add_to_clock >>
     simp[SimpL ``$==>``] >>
     disch_then(qspec_then `ack6` mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >>
     disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack8 = ack6 + _` >> pop_assum kall_tac >>
     simp[Once evaluate_def] >>
     last_x_assum drule >>
     qmatch_goalsub_abbrev_tac `refs_fupd (K a1)` >>
     disch_then(qspec_then `empty_state with refs := a1` mp_tac) >>
     simp[] >>
     qunabbrev_tac `a1` >> strip_tac >>
     Q.REFINE_EXISTS_TAC `extra + 1` >>
     simp[dec_clock_def] >>
     Q.ISPEC_THEN `s2 with refs := s1.refs ++ refs` dxrule evaluate_empty_state_norel >>
     strip_tac >>
     qmatch_asmsub_abbrev_tac `clock_fupd (K ack9)` >>
     Q.REFINE_EXISTS_TAC `extra + ack9` >>
     drule evaluate_add_to_clock >>
     simp[SimpL ``$==>``] >>
     disch_then(qspec_then `ack8` mp_tac) >>
     strip_tac >>
     dxrule evaluate_add_to_clock >>
     simp[] >> disch_then kall_tac >>
     PURE_REWRITE_TAC [ADD_ASSOC] >>
     qpat_abbrev_tac `ack10 = ack8 + _` >> pop_assum kall_tac >>
     simp[evaluate_def,namespaceTheory.nsOptBind_def,ml_progTheory.nsLookup_nsBind_compute,
          do_app_def,store_lookup_def,EL_APPEND_EQN,copy_array_def,integerTheory.INT_ABS,
          LUPDATE_APPEND,LUPDATE_def] >>
     IF_CASES_TAC >-
       (spose_not_then kall_tac >> pop_assum mp_tac >> intLib.COOPER_TAC) >>
     simp[store_assign_def,store_v_same_type_def,EL_APPEND_EQN,
          semanticPrimitivesTheory.state_component_equality,LUPDATE_APPEND,
          REWRITE_RULE [ADD1] REPLICATE,LUPDATE_def,TAKE_TAKE] >>
     rw[pad_def,DROP_NIL] >> intLib.COOPER_TAC));

val _ = export_theory ();
