open preamble bigstepSemTheory chorSemTheory confluenceTheory;

val _ = new_theory "bigstepProof";

val [_,RTC_EXTEND] = CONJUNCTS(SPEC_ALL RTC_RULES);

val evaluate_sound = Q.store_thm("evaluate_sound",
  `!s c s'. evaluate s c = SOME s' ==> trans_s (s,c) (s',Nil)`,
  Induct_on `c`
  >> rpt strip_tac >> fs[evaluate_def,trans_s_def] >> every_case_tac >> fs[]
  >> rpt(first_x_assum drule >> DISCH_TAC)
  >> match_mp_tac RTC_EXTEND >> PURE_ONCE_REWRITE_TAC[CONJ_SYM]
  >> asm_exists_tac >> fs[]
  >> metis_tac[trans_rules]);

val evaluate_complete = Q.store_thm("evaluate_complete",
  `!s c s'. trans_s (s,c) (s',Nil) ==> evaluate s c = SOME s'`,
  rpt gen_tac
  >> qpat_abbrev_tac `sc = (s,c)`
  >> qpat_abbrev_tac `sn = (s',Nil)`
  >> strip_tac
  >> ntac 2 (qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s`,`c`,`s'`])
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`sn`])
  >> PURE_ONCE_REWRITE_TAC [trans_s_def]
  >> ho_match_mp_tac RTC_STRONG_INDUCT
  >> rpt strip_tac >> rveq >> fs[]
  >- (rveq >> fs[evaluate_def])
  >> Cases_on `sc'` >> fs[]
  >> rename1 `trans (s1,c1) alpha (s2,c2)`
  >> rename1 `evaluate _ _ = SOME s3`
  >> qpat_x_assum `evaluate _ _ = _` mp_tac
  >> qpat_x_assum `_^* _ _` kall_tac (* mp_tac *)
  >> pop_assum mp_tac
(*  >> qmatch_asmsub_abbrev_tac `trans sc1 alpha sc2`*)
(*  >> ntac 2 (qpat_x_assum `Abbrev _` (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def]))*)
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`s1`,`s2`,`s3`,`c1`,`c2`,`alpha`])
  >> Induct_on `c1`
  >> rpt strip_tac >> fs[] >> rveq
  >- (* Nil *)
   (qpat_x_assum `trans _ _ _` (mp_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
    >> fs[evaluate_def])
  >- (* If *)
   (qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
    >> fs[evaluate_def] >> rveq >> fs[]
    >> fs[evaluate_def] >> every_case_tac >> rveq >> fs[]
    >> imp_res_tac confluenceTheory.lookup_fresh_after_trans >> fs[]
    >> pop_assum drule >> DISCH_TAC
    >> fs[]
    >> metis_tac[])
  >- (* Com *)
   (rename1 `evaluate _ (Com p1 v1 p v2 _) = _`
    >> qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
    >> fs[evaluate_def] >> rveq >> fs[]
    >> fs[evaluate_def] >> every_case_tac >> rveq >> fs[]
    >> imp_res_tac confluenceTheory.lookup_fresh_after_trans
    >> pop_assum(qspec_then `p1` assume_tac) >> rfs[] >> fs[]
    >> imp_res_tac confluenceTheory.lookup_unwritten_after_trans
    >> pop_assum(qspecl_then [`v1`,`p1`] assume_tac) >> rfs[] >> fs[]
    >> drule semantics_add_irrelevant_state_tup >> disch_then drule
    >> disch_then (qspecl_then [`v2`,`x`] assume_tac) >> first_x_assum drule
    >> disch_then drule >> simp[])
  >- (* Let *)
   (rename1 `evaluate _ (Let v p f vl c1) = _`
    >> qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
    >> fs[evaluate_def] >> rveq >> fs[]
    >> fs[evaluate_def] >> every_case_tac >> rveq >> fs[]
    >> conj_tac
    >- (imp_res_tac confluenceTheory.map_lookup_fresh_after_trans' >> fs[])
    >> imp_res_tac confluenceTheory.map_lookup_fresh_after_trans_tup
    >> fs[]
    >> qpat_abbrev_tac `a1 = f _`
    >> drule semantics_add_irrelevant_state_tup >> disch_then drule
    >> disch_then (qspecl_then [`v`,`a1`] assume_tac) >> first_x_assum drule
    >> disch_then drule >> simp[])
  >- (* Sel *)
   (qpat_x_assum `trans _ _ _` (assume_tac o PURE_ONCE_REWRITE_RULE [trans_cases])
    >> fs[evaluate_def] >> rveq >> fs[]
    >> fs[evaluate_def] >> every_case_tac >> rveq >> fs[]
    >> imp_res_tac confluenceTheory.lookup_fresh_after_trans >> fs[]
    >> pop_assum drule >> DISCH_TAC
    >> fs[]
    >> metis_tac[]));

val _ = export_theory ()
