open preamble bigstepSemTheory semBakeryTheory;

val _ = new_theory "bigstepProof";

val [_,RTC_EXTEND] = CONJUNCTS(SPEC_ALL RTC_RULES);

val _ = Q.store_thm("evaluate_sound",
  `!s c s'. evaluate s c = SOME s' ==> trans_s (s,c) (s',Nil)`,
  Induct_on `c`
  >> rpt strip_tac >> fs[evaluate_def,trans_s_def] >> every_case_tac >> fs[]
  >> rpt(first_x_assum drule >> DISCH_TAC)
  >> match_mp_tac RTC_EXTEND >> PURE_ONCE_REWRITE_TAC[CONJ_SYM]
  >> asm_exists_tac >> fs[]
  >> metis_tac[trans_rules]);

val _ = Q.store_thm("evaluate_complete",
  `!s c s'. trans_s (s,c) (s',Nil) ==> evaluate s c = SOME s'`,
  cheat);

val _ = export_theory ()
