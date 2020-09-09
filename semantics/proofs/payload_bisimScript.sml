open preamble payloadSemTheory payloadLangTheory payloadPropsTheory choreoUtilsTheory bisimulationTheory;

val _ = new_theory "payload_bisim";


(* An ungodly simulation preorder where
   visible actions are mimicked by single actions,
   and tau actions are mimicked by sequences of
   tau actions, with the restruction that the
   RHS process must have strictly more taus than the
   LHS process.
 *)
val (tausim_rules,tausim_coind,tausim_cases) =
  Hol_coreln
    ‘∀p1 q1.
        (∀p2 α.
          trans conf p1 α p2 ∧ α ≠ LTau ⇒
          ∃q2. trans conf q1 α q2 ∧ tausim conf p2 q2) ∧
        (∀q2 α.
          trans conf q1 α q2 ∧ α ≠ LTau ⇒
          ∃p2. trans conf p1 α p2 ∧ tausim conf p2 q2) ∧
        (∀p2.
          trans conf p1 LTau p2 ⇒
          ∃q2. (reduction conf)⁺ q1 q2 ∧ tausim conf p2 q2) ∧
        (∀q2.
          trans conf q1 LTau q2 ⇒
          ∃p2. RC(reduction conf) p1 p2 ∧ tausim conf p2 q2)
     ⇒
     tausim conf p1 q1’

Theorem bisim_IMP_tausim:
  ∀conf p q. BISIM_REL (trans conf) p q ⇒ tausim conf p q
Proof
  strip_tac >>
  ho_match_mp_tac tausim_coind >>
  rw[] >>
  qhdtm_x_assum ‘BISIM_REL’ (assume_tac o ONCE_REWRITE_RULE[BISIM_REL_cases]) >>
  fs[FORALL_AND_THM] >>
  res_tac >>
  fs[RC_DEF,RIGHT_AND_OVER_OR,EXISTS_OR_THM,reduction_def] >>
  goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
  simp[reduction_def]
QED

Theorem tausim_IMP_wbisim:
  ∀conf p q. tausim conf p q ⇒ WBISIM_REL (trans conf) LTau p q
Proof
  strip_tac >>
  ho_match_mp_tac WBISIM_REL_coind >>
  rw[] >>
  qhdtm_x_assum ‘tausim’ (assume_tac o ONCE_REWRITE_RULE[tausim_cases]) >>
  fs[FORALL_AND_THM] >>
  res_tac >>
  TRY(goal_assum(resolve_then (Pos hd) mp_tac TS_IMP_WTS) >>
      simp[] >> NO_TAC) >>
  fs[] >>
  fs[ETS_def,GSYM reduction_def] >>
  CONV_TAC(DEPTH_CONV ETA_CONV) >>
  metis_tac[TC_RTC,RC_RTC]
QED

Theorem tausim_refl:
  ∀conf p. tausim conf p p
Proof
  strip_tac >>
  ‘∀p q. p = q ⇒ tausim conf p q’ suffices_by simp[] >>
  ho_match_mp_tac tausim_coind >>
  rw[GSYM reduction_def] >>
  metis_tac[RC_DEF,TC_SUBSET]
QED

Theorem tausim_trans:
  ∀conf p q r. tausim conf p q ∧ tausim conf q r ⇒ tausim conf p r
Proof
  strip_tac >>
  CONV_TAC(QUANT_CONV(SWAP_FORALL_CONV)) >>
  simp[GSYM PULL_EXISTS] >>
  ho_match_mp_tac tausim_coind >> rw[]
  >- (rpt(qhdtm_x_assum ‘tausim’ (assume_tac o ONCE_REWRITE_RULE[tausim_cases])) >>
      metis_tac[])
  >- (rpt(qhdtm_x_assum ‘tausim’ (assume_tac o ONCE_REWRITE_RULE[tausim_cases])) >>
      metis_tac[])
  >- (rpt(qhdtm_x_assum ‘tausim’ (assume_tac o ONCE_REWRITE_RULE[tausim_cases])) >>
      fs[FORALL_AND_THM] >>
      res_tac >> fs[PULL_EXISTS] >>
      goal_assum(drule_at Any) >>
      qpat_x_assum ‘∀q2. trans conf q LTau _ ⇒ ∃q2. TC _ _ _ ∧ _’ mp_tac >>
      qpat_x_assum ‘TC _ _ _’ mp_tac >>
      rpt(pop_assum kall_tac) >>
      MAP_EVERY qid_spec_tac [‘q2’] >>
      ho_match_mp_tac TC_INDUCT_ALT_RIGHT >>
      rw[reduction_def] >>
      res_tac >>
      rpt(qhdtm_x_assum ‘tausim’ (assume_tac o ONCE_REWRITE_RULE[tausim_cases])) >>
      fs[FORALL_AND_THM] >>
      res_tac >> fs[PULL_EXISTS] >>
      metis_tac[TC_RULES])
  >- (qhdtm_x_assum ‘tausim’ (assume_tac o ONCE_REWRITE_RULE[tausim_cases]) >>
      fs[FORALL_AND_THM] >>
      res_tac >> fs[PULL_EXISTS] >>
      fs[RC_DEF,RIGHT_AND_OVER_OR,EXISTS_OR_THM,reduction_def] >> rveq >>
      rpt(PRED_ASSUM is_forall kall_tac)
      >- metis_tac[] >>
      qpat_x_assum ‘tausim conf p q’ (assume_tac o ONCE_REWRITE_RULE[tausim_cases]) >>
      fs[FORALL_AND_THM] >>
      res_tac >> fs[PULL_EXISTS] >>
      fs[RC_DEF,RIGHT_AND_OVER_OR,EXISTS_OR_THM,reduction_def] >> rveq >>
      rpt(PRED_ASSUM is_forall kall_tac) >>
      metis_tac[])
QED

val _ = export_theory ();
