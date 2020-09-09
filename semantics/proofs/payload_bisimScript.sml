open preamble payloadSemTheory payloadLangTheory payloadPropsTheory choreoUtilsTheory bisimulationTheory;

val _ = new_theory "payload_bisim";

(* Strong bisimulation up-to BISIM_REL *)
(* TODO: upstream to bisimulationTheory? *)
Theorem BISIM_REL_strong_coind:
  ∀ts R.
    (∀p q.
       R p q ⇒
       ∀l.
         (∀p'. ts p l p' ⇒ ∃q'. ts q l q' ∧ (R p' q' ∨ BISIM_REL ts p' q')) ∧
         ∀q'. ts q l q' ⇒ ∃p'. ts p l p' ∧ (R p' q' ∨ BISIM_REL ts p' q')) ⇒
    ∀p q. R p q ⇒ BISIM_REL ts p q
Proof
  ntac 3 strip_tac >>
  ‘∀p q. R p q ∨ BISIM_REL ts p q ⇒ BISIM_REL ts p q’ suffices_by simp[] >>
  ho_match_mp_tac BISIM_REL_coind >>
  rw[LEFT_AND_OVER_OR,EXISTS_OR_THM] >>
  metis_tac[BISIM_REL_cases]
QED

(* Structural congruence rules for strong bisimilarity *)

Theorem bisim_par_sym:
  ∀conf p q. BISIM_REL (trans conf) (NPar p q) (NPar q p)
Proof
  strip_tac >>
  ‘∀pq qp p q. pq = NPar p q ∧ qp = NPar q p ⇒ BISIM_REL (trans conf) pq qp’ suffices_by fs[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac BISIM_REL_coind >>
  rw[] >>
  qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >>
  fs[] >> rveq >>
  rw[Once trans_cases] >> metis_tac[]
QED

Theorem bisim_par_assoc:
  ∀conf p q r. BISIM_REL (trans conf) (NPar p (NPar q r)) (NPar (NPar p q) r)
Proof
  strip_tac >>
  ‘∀pq qp p q r. pq = NPar p (NPar q r) ∧ qp = NPar (NPar p q) r ⇒ BISIM_REL (trans conf) pq qp’ suffices_by fs[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac BISIM_REL_coind >>
  rw[] >>
  qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >>
  fs[] >> rveq >>
  TRY(qpat_x_assum ‘trans conf (NPar _ _) _ _’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases])) >>
  fs[] >> rveq >>
  metis_tac[trans_par_l,trans_par_r,trans_com_l,trans_com_r]
QED

Theorem BISIM_TRANS:
  ∀a b c. BISIM_REL R a b ∧ BISIM_REL R b c ⇒ BISIM_REL R a c
Proof
  metis_tac[BISIM_REL_IS_EQUIV_REL,equivalence_def,transitive_def]
QED

Theorem BISIM_SYM:
  BISIM_REL R a b ⇒ BISIM_REL R b a
Proof
  metis_tac[BISIM_REL_IS_EQUIV_REL,equivalence_def,symmetric_def]
QED

Theorem junkcong_bisim:
  ∀fv p1 q1 conf. junkcong fv p1 q1 ⇒ BISIM_REL (trans conf) p1 q1
Proof
  rw[BISIM_REL_def] >>
  qexists_tac ‘junkcong fv’ >> simp[] >>
  rw[BISIM_def] >>
  metis_tac[payloadPropsTheory.junkcong_trans_pres,payloadPropsTheory.junkcong_sym]
QED

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

Theorem tausim_par_left:
  ∀conf p q r s. tausim conf p r ⇒ tausim conf (NPar p q) (NPar r q)
Proof
  strip_tac >>
  ‘∀pq rs p q r. pq = NPar p q ∧ rs = NPar r q ∧ tausim conf p r ⇒ tausim conf pq rs’
    suffices_by simp[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac tausim_coind >> rw[]
  >- (qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >> fs[] >>
      rveq
      >- ((* par_l *)
          metis_tac[tausim_cases,trans_par_l])
      >- ((* par_r *)
          metis_tac[trans_par_r]))
  >- (qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >> fs[] >>
      rveq
      >- ((* par_l *)
          metis_tac[tausim_cases,trans_par_l])
      >- ((* par_r *)
          metis_tac[trans_par_r]))
  >- (qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >> fs[] >>
      rveq
      >- ((* com_l *)
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          simp[reduction_def] >>
          metis_tac[tausim_cases,label_distinct,trans_com_l])
      >- ((* com_r *)
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          simp[reduction_def] >>
          metis_tac[tausim_cases,label_distinct,trans_com_r])
      >- ((* par_l *)
          metis_tac[reduction_TC_par_l,tausim_cases])
      >- ((* par_l *)
          goal_assum(resolve_then (Pos hd) mp_tac TC_SUBSET) >>
          metis_tac[trans_par_r,reduction_def]))
  >- (qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >> fs[] >>
      rveq
      >- ((* com_l *)
          goal_assum(resolve_then (Pos hd) mp_tac RC_SUBSET) >>
          simp[reduction_def] >>
          metis_tac[tausim_cases,label_distinct,trans_com_l])
      >- ((* com_r *)
          goal_assum(resolve_then (Pos hd) mp_tac RC_SUBSET) >>
          simp[reduction_def] >>
          metis_tac[tausim_cases,label_distinct,trans_com_r])
      >- ((* par_l *)
          metis_tac[RC_DEF,tausim_cases,trans_par_l,reduction_def])
      >- ((* par_l *)
          metis_tac[RC_DEF,trans_par_r,reduction_def]))
QED

Theorem tausim_par_sym:
  ∀conf p q. tausim conf (NPar p q) (NPar q p)
Proof
  rpt strip_tac >>
  match_mp_tac bisim_IMP_tausim >>
  MATCH_ACCEPT_TAC bisim_par_sym
QED

Theorem tausim_par_assoc:
  ∀conf p q r. tausim conf (NPar p (NPar q r)) (NPar (NPar p q) r)
Proof
  rpt strip_tac >>
  match_mp_tac bisim_IMP_tausim >>
  MATCH_ACCEPT_TAC bisim_par_assoc
QED

Theorem tausim_par_right:
  ∀conf p q r s. tausim conf q r ⇒ tausim conf (NPar p q) (NPar p r)
Proof
  metis_tac[tausim_trans,tausim_par_sym,tausim_par_left]
QED

Theorem tausim_par:
  ∀conf p q r s. tausim conf p s ∧ tausim conf q r ⇒ tausim conf (NPar p q) (NPar s r)
Proof
  metis_tac[tausim_trans,tausim_par_left,tausim_par_right]
QED

val _ = export_theory ();
