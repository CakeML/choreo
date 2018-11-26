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

val padv_correct = Q.store_thm("padv_correct",`
  !env conf l lv le s0 s1 s2.
  env_asm env conf /\
  LIST_TYPE ^WORD8 l lv /\
  evaluate$evaluate s1 env [le] = (s2, Rval [lv])
  ==>
  ?ck1 ck2 refs' num lv'.
  evaluate$evaluate (s1 with clock:= ck1) env [App Opapp [padv conf; le]] =
           (s2 with <|clock := ck2; refs := APPEND s1.refs refs'|>, Rval [Loc num]) /\
  store_lookup num (APPEND s1.refs refs') = SOME(W8array(pad conf l))
  `,
  rpt strip_tac >>
  drule evaluate_add_to_clock >>
  simp[] >>
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
  Q.ISPEC_THEN `s2` drule evaluate_empty_state_norel >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `clock_fupd (K ack)` >>
  Q.REFINE_EXISTS_TAC `extra + ack` >>
  drule evaluate_add_to_clock >>
  simp[SimpL ``$==>``] >>
  disch_then(qspec_then `s2.clock` mp_tac) >>
  strip_tac >>
  dxrule evaluate_add_to_clock >>
  simp[] >>
  disch_then kall_tac >>
  fs[NUM_def,INT_def] >>  
  simp[do_app_def] >>
  simp[terminationTheory.do_eq_def,lit_same_type_def,Boolv_def,do_if_def] >>
  cheat
);


val _ = export_theory ();
