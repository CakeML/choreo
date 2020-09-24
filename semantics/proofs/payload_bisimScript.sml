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

(* Nil is always bisimilar to Nil (regardless of state) *)
Theorem BISIM_REL_Nil:
  ∀conf p s s'.
    BISIM_REL (trans conf) (NEndpoint p s Nil) (NEndpoint p s' Nil)
Proof
  ntac 2 strip_tac >>
  ‘∀n1 n2 s s'.
    n1 = NEndpoint p s Nil ∧ n2 = NEndpoint p s' Nil ⇒
    BISIM_REL (trans conf) n1 n2’
    suffices_by simp[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac bisimulationTheory.BISIM_REL_coind >>
  rw[] >>
  fs[Once trans_cases]
QED

Theorem bisim_par_left:
  ∀conf p q r s. BISIM_REL (trans conf) p r ⇒ BISIM_REL (trans conf) (NPar p q) (NPar r q)
Proof
  strip_tac >>
  ‘∀pq rs p q r. pq = NPar p q ∧ rs = NPar r q ∧ BISIM_REL (trans conf) p r ⇒ BISIM_REL (trans conf) pq rs’
    suffices_by simp[] >>
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
  ho_match_mp_tac BISIM_REL_coind >> rw[] >>
  qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >> fs[] >>
  rveq >>
  metis_tac[BISIM_REL_cases,trans_com_l,trans_com_r,trans_par_l,trans_par_r]
QED

Theorem bisim_trans:
  ∀R p q r. BISIM_REL R p q ∧ BISIM_REL R q r ⇒ BISIM_REL R p r
Proof
  metis_tac[bisimulationTheory.BISIM_REL_IS_EQUIV_REL,equivalence_def,transitive_def]
QED

Theorem bisim_sym:
  ∀R p q. BISIM_REL R p q ⇒ BISIM_REL R q p
Proof
  metis_tac[bisimulationTheory.BISIM_REL_IS_EQUIV_REL,equivalence_def,symmetric_def]
QED

Theorem bisim_refl:
  ∀R p. BISIM_REL R p p
Proof
  metis_tac[bisimulationTheory.BISIM_REL_IS_EQUIV_REL,equivalence_def,reflexive_def]
QED

Theorem bisim_par_right:
  ∀conf p q r s. BISIM_REL (trans conf) q r ⇒ BISIM_REL (trans conf) (NPar p q) (NPar p r)
Proof
  metis_tac[bisim_trans,bisim_par_sym,bisim_par_left]
QED

Theorem bisim_par:
  ∀conf p q r s. BISIM_REL (trans conf) p s ∧ BISIM_REL (trans conf) q r ⇒ BISIM_REL (trans conf) (NPar p q) (NPar s r)
Proof
  metis_tac[bisim_trans,bisim_par_left,bisim_par_right]
QED

(* TODO: move to props *)
Theorem MEM_free_fun_names_endpoint_dsubst:
  ∀e dn e'.
  MEM x (free_fun_names_endpoint (dsubst e dn e')) ⇒
  MEM x (free_fun_names_endpoint e) ∨
  MEM x (free_fun_names_endpoint e')
Proof
  Induct >> rw[free_fun_names_endpoint_def,dsubst_def] >>
  fs[MEM_FILTER] >> res_tac >> fs[]
QED

Definition used_closures_rel_def:
  used_closures_rel s (Closure vars1 (fs1,bds1) e1) (Closure vars2 (fs2,bds2) e2) ⇔
  e1 = e2 ∧ bds1 = bds2 ∧ vars1 = vars2 ∧
  ∀dn. MEM dn (free_fun_names_endpoint e1) ∧ dn ∉ s ⇒
    ((ALOOKUP fs1 dn = NONE ∧ ALOOKUP fs2 dn = NONE) ∨
     (∃cl1 cl2.
        ALOOKUP fs1 dn = SOME cl1 ∧ ALOOKUP fs2 dn = SOME cl2 ∧
        (ALOOKUP fs1 dn = SOME cl1 ∧ ALOOKUP fs2 dn = SOME cl2 ⇒ used_closures_rel {dn} cl1 cl2)
     ))
Termination
  WF_REL_TAC ‘inv_image $< (closure_size o FST o SND)’ >>
  rw[closure_size_def] >> imp_res_tac ALOOKUP_MEM >>
  imp_res_tac closure_size_MEM >>
  DECIDE_TAC
End

Definition used_closures_endpoint_rel_def:
  used_closures_endpoint_rel n1 n2 ⇔
  ∃p (s:closure state) e fs1 fs2.
    n1 = NEndpoint p (s with funs := fs1) e ∧
    n2 = NEndpoint p (s with funs := fs2) e ∧
    (∀dn. MEM dn (free_fun_names_endpoint e) ⇒
          ((ALOOKUP fs1 dn = NONE ∧ ALOOKUP fs2 dn = NONE) ∨
           (∃cl1 cl2.
             ALOOKUP fs1 dn = SOME cl1 ∧ ALOOKUP fs2 dn = SOME cl2 ∧
             used_closures_rel {dn} cl1 cl2)))
End

(* TODO: move? *)
Triviality final_intermediate_imps:
  (final d ⇒ ~intermediate d) ∧
  (intermediate d ⇒ ~final d)
Proof
  metis_tac[intermediate_final_IMP]
QED

Theorem used_closures_rel_refl:
  ∀s cl1. used_closures_rel s cl1 cl1
Proof
  ‘∀s cl1 cl2. cl1 = cl2 ⇒ used_closures_rel s cl1 cl2’ suffices_by simp[] >>
  ho_match_mp_tac used_closures_rel_ind >>
  rw[used_closures_rel_def] >>
  Cases_on ‘ALOOKUP fs1 dn’ >> fs[] >>
  metis_tac[]
QED

Theorem bisim_used_closures_rel:
  ∀conf n1 n2.
    used_closures_endpoint_rel n1 n2 ⇒
    BISIM_REL (trans conf) n1 n2
Proof
  strip_tac >>
  ho_match_mp_tac bisimulationTheory.BISIM_REL_coind >>
  rw[] >>
  fs[used_closures_endpoint_rel_def] >> rveq
  >>
    (qhdtm_x_assum ‘trans’ (strip_assume_tac o ONCE_REWRITE_RULE[trans_cases]) >>
     fs[free_fun_names_endpoint_def] >> rveq >>
     rw[Once trans_cases] >> fs[] >>
     imp_res_tac final_intermediate_imps >> fs[]
     >- (ntac 2 (goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL)) >> metis_tac[])
     >- (ntac 2 (goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL)) >> metis_tac[])
     >- (ntac 2 (goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL)) >> metis_tac[])
     >- (Q.REFINE_EXISTS_TAC ‘<|bindings := _; funs := _; queues := _|>’ >> simp[])
     >- (Q.REFINE_EXISTS_TAC ‘_ with queues := _’ >> simp[] >> metis_tac[])
     >- (ntac 2 (goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL)) >> metis_tac[])
     >- (ntac 2 (goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL)) >> metis_tac[])
     >- (Q.REFINE_EXISTS_TAC ‘(_:closure state) with <|bindings := _; funs := _|>’ >> simp[] >>
         metis_tac[])
     >- (goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
         goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
         rw[] >>
         imp_res_tac MEM_free_fun_names_endpoint_dsubst >>
         fs[free_fun_names_endpoint_def])
     >- (goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
         goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
         fs[FILTER_APPEND,MEM_FILTER] >> rveq >> fs[LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
         rw[] >>
         rw[used_closures_rel_def] >>
         metis_tac[])
     >- (fs[PULL_EXISTS] >> rveq >>
         TRY(Cases_on ‘cl2’ ORELSE Cases_on ‘cl1’) >>
         rename1 ‘Closure _ fb _’ >> Cases_on ‘fb’ >> fs[used_closures_rel_def] >>
         Q.REFINE_EXISTS_TAC ‘_ with <|bindings := _|>’ >> simp[] >>
         goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
         goal_assum(resolve_then (Pos hd) mp_tac EQ_REFL) >>
         rveq >> rw[] >> fs[used_closures_rel_def] >>
         metis_tac[]))
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

Theorem tausim_strong_coind:
  ∀conf R.
    (∀p q.
       R p q ⇒
       (∀p2 α.
          trans conf p α p2 ∧ α ≠ LTau ⇒
          ∃q2. trans conf q α q2 ∧ (R p2 q2 ∨ tausim conf p2 q2)) ∧
       (∀q2 α.
          trans conf q α q2 ∧ α ≠ LTau ⇒
          ∃p2. trans conf p α p2 ∧ (R p2 q2 ∨ tausim conf p2 q2)) ∧
       (∀p2.
          trans conf p LTau p2 ⇒
          ∃q2. (reduction conf)⁺ q q2 ∧ (R p2 q2 ∨ tausim conf p2 q2)) ∧
       ∀q2.
         trans conf q LTau q2 ⇒
         ∃p2. RC (reduction conf) p p2 ∧ (R p2 q2 ∨ tausim conf p2 q2)) ⇒
    ∀p q. R p q ⇒ tausim conf p q
Proof
  rpt gen_tac >> strip_tac >>
  ‘∀p q. R p q ∨ tausim conf p q ⇒ tausim conf p q’ suffices_by simp[] >>
  ho_match_mp_tac tausim_coind >>
  rw[] >> metis_tac[tausim_cases]
QED

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
