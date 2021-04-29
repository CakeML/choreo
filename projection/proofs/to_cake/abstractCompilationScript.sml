open HolKernel Parse boolLib bossLib;

open relationTheory arithmeticTheory
val _ = new_theory "abstractCompilation";

fun SRULE ths = SIMP_RULE (srw_ss()) ths

Definition postcloud_def:
  postcloud c sR tR s t ⇔ tR꙳ (c s) t ∧ ∀s'. sR s s' ⇒ tR⁺ t (c s')
End

Theorem postcloud_NF:
  postcloud c sR tR s t ∧ (∀t'. ¬tR t t') ⇒ ∀s'. ¬sR s s'
Proof
  simp[postcloud_def] >> rpt strip_tac >> first_x_assum drule >>
  metis_tac[TC_CASES1]
QED


Definition simulates_def:
  simulates sim R1 R2 ⇔
    ∀a0 a b0. sim a0 b0 ∧ R1 a0 a ⇒ ∃b. sim a b ∧ R2 b0 b
End

Theorem simulates_RTC:
  simulates sim R1 R2 ⇒ simulates sim R1꙳ R2꙳
Proof
  simp[simulates_def] >> strip_tac >> Induct_on ‘RTC’ >>
  metis_tac[RTC_RULES]
QED

Theorem simulatesRC_RTC:
  simulates sim R1 (RC R2) ⇒ simulates sim R1꙳ R2꙳
Proof
  simp[simulates_def] >> strip_tac >> Induct_on ‘RTC’ >>
  metis_tac[RTC_RULES, RC_DEF]
QED


Theorem forward_implies_back:
  (∀s1 s2. sR s1 s2 ⇒ tR⁺ (compile s1) (compile s2)) ∧
  (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2)
  ⇒
  ∀s0 t0 t. postcloud compile sR tR s0 t0 ∧ tR t0 t ⇒
            ∃s. postcloud compile sR tR s t ∧ RC sR s0 s
Proof
  rw[postcloud_def] >>
  reverse (Cases_on ‘∃s. compile s = t ∧ sR s0 s’)
  >- (gvs[] >> qexists_tac ‘s0’ >>
      simp[RC_DEF] >> conj_tac
      >- metis_tac[RTC_CASES2] >>
      rw[] >> first_x_assum drule >>
      simp[SimpL “$==>”, Once TC_CASES1] >>
      metis_tac[]) >>
  gvs[] >> qexists_tac ‘s’ >> simp[RC_DEF]
QED

Theorem forwardTC_back_simulates:
  simulates (λs t. t = compile s) sR tR⁺ ∧
  (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2)
  ⇒
  simulates (postcloud compile sR tR)ᵀ tR (RC sR)
Proof
  simp[simulates_def] >> metis_tac[forward_implies_back]
QED

Definition triR_def:
  triR R n e1 e2 ⇔ ∃e. NRC R n e1 e ∧ R꙳ e2 e ∧ (n = 0 ⇒ e2 = e)
End

Definition tcdistance_def:
  tcd R a b = (@n. NRC R n a b) - 1
End

Theorem TC_triR0:
  R⁺ a b ⇒ ∃n. triR R (n + 1) a b
Proof
  simp[triR_def, TC_eq_NRC, ADD1] >> metis_tac[RTC_REFL]
QED

Theorem TC_triR[local] =
        TC_triR0 |> Q.GENL[‘R’, ‘a’, ‘b’]
                 |> SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]

val tcd_def = new_specification("tcd_def", ["tcd"], TC_triR)

Theorem triR_one_step_each:
  R a0 a ∧ R b0 b ∧ triR R n a b ⇒ triR R (n + 1) a0 b0
Proof
  simp[triR_def] >> strip_tac >> ONCE_REWRITE_TAC [ADD_COMM] >>
  irule_at Any NRC_ADD_I >> simp[] >> metis_tac[RTC_RULES]
QED

Theorem triR_step1:
  R a0 a ∧ triR R n a b ⇒ triR R (n + 1) a0 b
Proof
  simp[triR_def] >> strip_tac >> ONCE_REWRITE_TAC [ADD_COMM] >>
  irule_at Any NRC_ADD_I >> simp[] >> metis_tac[RTC_RULES]
QED

Theorem triR_steps10:
  R꙳ a0 a ∧ triR R n a b ⇒ ∃d. triR R (n + d) a0 b
Proof
  simp[triR_def] >> strip_tac >> irule_at Any NRC_ADD_I >>
  ntac 2 (first_assum $ irule_at Any) >> metis_tac[RTC_eq_NRC]
QED

Theorem RTC_steps =
        RTC_eq_NRC |> iffLR
                   |> SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]

val rtd_def = new_specification("rtd_def", ["rtd"], RTC_steps)

Theorem triR_steps1:
  R꙳ a0 a ∧ triR R n a b ⇒ triR R (n + rtd R a0 a) a0 b
Proof
  strip_tac >> drule rtd_def >> gs[triR_def] >>
  metis_tac[NRC_ADD_I, ADD_COMM]
QED

Theorem triR_REFL[simp]:
  ∀x. triR R 0 x x
Proof
  simp[triR_def]
QED

Theorem triR_step1R:
  0 < n ∧ triR R n a b ∧ R b0 b ⇒ triR R n a b0
Proof
  simp[triR_def] >> metis_tac[RTC_RULES]
QED

Theorem triR_stepsR:
  0 < n ∧ R꙳ b0 b ∧ triR R n a b ⇒ triR R n a b0
Proof
  simp[triR_def] >> metis_tac[RTC_CASES_RTC_TWICE]
QED

CoInductive mayloop:
  ∀t0 t. mayloop tR t ∧ tR t0 t ⇒ mayloop tR t0
End

Theorem RC_mayloop[simp]:
  ∀x. mayloop (RC R) x
Proof
  ‘∀x. K T x ⇒ mayloop (RC R) x’ suffices_by simp[] >>
  ho_match_mp_tac mayloop_coind >> simp[EXISTS_OR_THM, RC_DEF]
QED

Definition mustloop_def:
  mustloop R x ⇔ ∀y. RTC R x y ⇒ ∃z. R y z
End

Theorem mustloop_mayloop:
  ∀x. mustloop R x ⇒ mayloop R x
Proof
  ho_match_mp_tac mayloop_coind >> rw[] >>
  rename [‘mustloop R x’] >>
  ‘∃y. R x y’ by metis_tac[RTC_REFL, mustloop_def] >>
  ‘∀z. R꙳ y z ⇒ R꙳ x z’ by metis_tac[RTC_RULES] >>
  ‘mustloop R y’ by metis_tac[mustloop_def] >> metis_tac[]
QED

Theorem det_term_xor_mayloop:
  (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2) ⇒
  ∀t0. ((∃t. nf tR t ∧ RTC tR t0 t) ⇔ ¬mayloop tR t0)
Proof
  strip_tac >> simp[FORALL_AND_THM, EQ_IMP_THM, PULL_EXISTS] >> conj_tac
  >- (Induct_on ‘RTC’ >> rw[]
      >- (gs[nf_def] >> simp[Once mayloop_cases]) >>
      gs[] >> simp[Once mayloop_cases] >> metis_tac[]) >>
  CONV_TAC (BINDER_CONV CONTRAPOS_CONV) >> simp[] >>
  ho_match_mp_tac mayloop_coind >> rw[] >>
  gs[nf_def] >> metis_tac[RTC_RULES]
QED

Theorem det_may_EQ_mustloop:
  (∀x y1 y2. R x y1 ∧ R x y2 ⇒ y1 = y2) ⇒
  ∀x. mayloop R x ⇔ mustloop R x
Proof
  metis_tac[nf_def, mustloop_def, det_term_xor_mayloop]
QED

        (*
Theorem TC_mayloop[simp]:
  mayloop R⁺ x ⇔ mayloop R x
Proof
  eq_tac
  >- (qid_spec_tac ‘x’ >> ho_match_mp_tac mayloop_coind >>
      simp[Once mayloop_cases, SimpL “$==>”] >> simp[PULL_EXISTS] >>
      simp[Once TC_CASES2, PULL_EXISTS, DISJ_IMP_THM, LEFT_AND_OVER_OR,
           FORALL_AND_THM] >> metis_tac[]
      >- metis_tac[] >>
      rename [‘R x y’, ‘R⁺ y t’] >> qexists_tac ‘y’ >> simp[] >>
      simp[Once mayloop_cases]) >>
  qid_spec_tac ‘x’ >> ho_match_mp_tac mayloop_coind >>
  metis_tac[TC_CASES1, mayloop_cases]
QED

Definition forward_sim_def:
  forward_sim sim sR tR ⇔
    ∃R. WF R ∧
        ∀s0 s t0.
          sim s0 t0 ∧ sR s0 s ⇒
          (∃t. tR t0 t ∧ sim s t) ∨ sim s t0 ∧ R s s0
End

Theorem mayloop_WFP:
  mayloop R x ⇔ ¬WFP Rᵀ x
Proof
  eq_tac
  >- (‘!x. WFP Rᵀ x ⇒ ¬mayloop R x’ suffices_by metis_tac[] >>
      ho_match_mp_tac WFP_STRONG_INDUCT >> simp[] >> rw[] >>
      simp[Once mayloop_cases] >> metis_tac[]) >>
  qid_spec_tac ‘x’ >> ho_match_mp_tac mayloop_coind >>
  simp[SimpL “$==>”, Once WFP_CASES] >> metis_tac[]
QED

Definition nf_matching_def:
  nf_matching sim sR tR ⇔
    ∀s t. nf sR s ∧ sim s t ⇒ ¬mayloop tR t
End

Definition postcloudR_def:
  postcloudR simR sR tR t s ⇔
    simR s t ∨
    ∃t0. simR s t0 ∧ tR⁺ t0 t ∧
         ∀t' s'. tR⁺ t0 t' ∧ tR⁺ t' t ⇒ ¬simR s' t'
End

Theorem forward_sim_TCinduce:
  forward_sim sim sR tR ⇒
  ∀s0 t0.
    sim s0 t0 ⇒
    WFP sRᵀ s0 ∧
    (∃s. sR꙳ s0 s ∧ sim s t0 ∧ nf sR s ∧ ∀s'. sR꙳ s0 s' ⇒ sim s' t0)
      ∨
    ∃s t. sR⁺ s0 s ∧ tR t0 t ∧ sim s t
Proof
  simp[forward_sim_def] >> rw[] >>
  qpat_x_assum ‘sim s0 t0’ mp_tac >>
  map_every qid_spec_tac [‘t0’, ‘s0’] >>
  drule WF_INDUCTION_THM >>
  disch_then (assume_tac o SRULE[RIGHT_FORALL_IMP_THM]) >>
  pop_assum ho_match_mp_tac >> rw[] >>
  Cases_on ‘∃s'. sR s0 s'’ >> gs[]
  >- (‘(∃t'. tR t0 t' ∧ sim s' t') ∨ sim s' t0 ∧ R s' s0’ by metis_tac[]
      >- metis_tac[TC_SUBSET] >>
      first_assum (drule_all_then strip_assume_tac)
      >- (Cases_on ‘∃s t. sR⁺ s0 s ∧ tR t0 t ∧ sim s t’ >> gs[] >>
          disj1_tac >> conj_tac
          >- (irule WFP_RULES >> simp[] >> qx_gen_tac ‘s1’ >> strip_tac >>
              ‘sim s1 t0 ∧ R s1 s0’ by metis_tac[TC_SUBSET] >>
              first_assum
                (fn th => first_x_assum
                            (fn ith => mp_then (Pos hd) mp_tac ith th)) >>
              disch_then $ drule_then strip_assume_tac >>
              metis_tac[TC_CASES1]) >>
          irule_at (Pos hd) (cj 2 RTC_RULES) >>
          first_assum $ irule_at (Pos hd) >>
          first_assum $ irule_at (Pos hd) >>
          simp[] >>
          simp[Once RTC_CASES1, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
          qx_genl_tac [‘ss’, ‘s1’] >> strip_tac >>
          ‘sim s1 t0 ∧ R s1 s0’ by metis_tac[TC_SUBSET] >>
          first_assum
            (fn th => first_x_assum
                        (fn ith => mp_then (Pos hd) mp_tac ith th)) >>
          disch_then $ drule_then strip_assume_tac >- metis_tac[] >>
          metis_tac[TC_CASES1]) >>
      metis_tac[TC_CASES1]) >>
  ‘∀s. sR꙳ s0 s ⇔ s = s0’ by metis_tac[RTC_CASES1] >> gs[] >>
  disj1_tac >> simp[nf_def] >> irule WFP_RULES >> simp[]
QED

Definition tterm_def:
  tterm sim sR tR t1 t0 ⇔
    tR t0 t1 ∧ forward_sim sim sR tR⁺ ∧ nf_matching sim sR tR ∧
    (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2) ∧
    ∃t00 s0. sim s0 t00 ∧ tR꙳ t00 t1 ∧
             ∀t'. tR⁺ t00 t' ∧ tR꙳ t' t1 ⇒
                  ∀s. sim s t' ⇒ ¬sR꙳ s0 s
End

Theorem WFP_RTC_along:
  ∀y x. WFP R y ∧ R꙳ x y ⇒ WFP R x
Proof
  Induct_on ‘WFP’ using WFP_STRONG_INDUCT >> rw[] >>
  qpat_x_assum ‘RTC R x y’ mp_tac >> simp[Once RTC_CASES2] >>
  metis_tac[]
QED

Theorem iterator_mayloop:
  (∀a. a ∈ P ⇒ it a ∈ P) ∧ (∀a b. a ∈ P ⇒ (R a b ⇔ b = it a)) ∧ x ∈ P ⇒
  mayloop R x
Proof
  strip_tac >> qpat_x_assum ‘x ∈ P’ mp_tac >> qid_spec_tac ‘x’ >>
  ho_match_mp_tac mayloop_coind >> metis_tac[]
QED

Theorem det_NRC_TC_lemma:
  (∀a b c. R a b ∧ R a c ⇒ b = c) ⇒
  NRC R n x y ∧ R⁺ x z ⇒
  (∃m. m < n ∧ NRC R m z y) ∨ R⁺ y z
Proof
  strip_tac >> map_every qid_spec_tac [‘n’, ‘x’, ‘y’, ‘z’] >>
  Induct_on ‘n’ >> simp[NRC, PULL_EXISTS] >> rpt gen_tac >>
  simp[SimpL “$==>”, Once TC_CASES1] >> strip_tac
  >- metis_tac[prim_recTheory.LESS_SUC_REFL] >>
  rename [‘NRC R n z1 y’, ‘R x z1’, ‘R x z2’, ‘R⁺ z2 z’] >>
  ‘z1 = z2’ by metis_tac[] >> (* gvs BUG *) pop_assum SUBST_ALL_TAC >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  rename [‘m < n’] >> disj1_tac >> qexists_tac ‘m’ >> simp[]
QED

Theorem forward_sim_overtakes_tR:
  (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2) ∧
  forward_sim sim sR tR⁺ ∧ nf_matching sim sR tR ⇒
  sim s0 t0 ∧ tR꙳ t0 w ⇒
  (∃s t. sR⁺ s0 s ∧ tR꙳ w t ∧ sim s t) ∨
  WFP tRᵀ w
Proof
  strip_tac >> simp[SimpL “$==>”, RTC_eq_NRC] >>
  simp[PULL_EXISTS] >> map_every qid_spec_tac [‘s0’, ‘t0’] >>
  completeInduct_on ‘n’ >> rpt strip_tac >>
  drule_then (drule_then strip_assume_tac) forward_sim_TCinduce
  >- (rename [‘nf sR s’] >>
      ‘¬mayloop tR t0’ by metis_tac[nf_matching_def] >>
      gs[mayloop_WFP] >> disj2_tac >>
      irule WFP_RTC_along >> simp[inv_MOVES_OUT] >>
      metis_tac[RTC_eq_NRC]) >>
  drule_all_then strip_assume_tac det_NRC_TC_lemma
  >- (first_x_assum $ drule_all_then strip_assume_tac
      >- metis_tac[TC_RULES] >>
      simp[]) >>
  metis_tac[TC_RTC]
QED
(*
Theorem WF_tterm[simp]:
  WF (tterm sim sR tR)
Proof
  simp[WF_DEF, tterm_def] >>
  Cases_on ‘forward_sim sim sR tR⁺’ >> simp[] >>
  Cases_on ‘nf_matching sim sR tR’ >> simp[PULL_EXISTS] >>
  Cases_on ‘∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2’ >> simp[] >>
  qx_gen_tac ‘tSet’ >> qx_gen_tac ‘w’ >> strip_tac >>
  ‘∀x. tSet x ⇔ x ∈ tSet’ by simp[IN_DEF] >>
  pop_assum (gs o single) >>
  Cases_on ‘∃d. d ∈ tSet ∧ ∀d'. tR d d' ⇒ d' ∉ tSet’ >> gs[]
  >- (qexists_tac ‘d’ >> simp[]) >>
  pop_assum (fn th => ‘∀d. d ∈ tSet ⇒ ∃d'. tR d d' ∧ d' ∈ tSet’
               by metis_tac[th]) >>
  pop_assum (qx_choose_then ‘next’ strip_assume_tac o
             SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM]) >>
  ‘∀d e. d ∈ tSet ⇒ (tR d e ⇔ e = next d)’ by metis_tac[] >>
  csimp[] >>
  Cases_on ‘∀t s. tR꙳ w t ⇒ ¬sim s t’ >> gs[]
  >- (Cases_on ‘∃t0 s0. tR꙳ t0 w ∧ sim s0 t0’ >> gs[]
      >- (drule_all_then strip_assume_tac forward_sim_overtakes_tR
          >- metis_tac[] >>
          ‘mayloop tR w’ by metis_tac[iterator_mayloop] >>
          gs[mayloop_WFP]) >>
      pop_assum (fn th => ‘∀t0 s0. tR꙳ t0 w ⇒ ¬sim s0 t0’ by metis_tac[th]) >>
      qexists_tac ‘w’ >> simp[] >> qx_genl_tac [‘t0’, ‘s0’] >>
      Cases_on ‘sim s0 t0’ >> simp[] >>
      Cases_on ‘tR꙳ t0 (next w)’ >> simp[PULL_EXISTS] >>
      drule_all_then strip_assume_tac forward_sim_overtakes_tR
      >- (rename [‘tR꙳ (next w) t’, ‘sim s t’] >>
          ‘tR w (next w)’ by simp[] >> metis_tac[RTC_RULES]) >>
      ‘tRᵀ (next w) w’ by simp[] >>
      ‘WFP tRᵀ w’ by (irule WFP_RULES >> simp[]) >>
      ‘mayloop tR w’ by metis_tac[iterator_mayloop] >> gs[mayloop_WFP]) >>




  Cases_on ‘∃t. tR꙳ w t ∧ ’
  Cases_on ‘∀s t. t ∈ tSet ⇒ ¬sim s t’ >> gs[]
  >- (qexists_tac ‘w’ >> rpt strip_tac >> simp[] >>
  reverse (Cases_on ‘∀t. t ∈ tSet ⇒ ∃t0 s0. tR꙳ t0 t ∧ sim s0 t0’) >> gs[]
  >- (qexists_tac ‘t’ >> simp[] >> metis_tac[cj 2 RTC_RULES_RIGHT1]

Theorem detforward_imp_backward:
  (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2) ∧
  nf_matching sim sR tR ∧
  forward_sim sim sR tR⁺ ⇒
  ∃sim'. sim ⊆ᵣ sim' ∧ forward_sim sim'ᵀ tR sR⁺
Proof
  simp[nf_matching_def] >> strip_tac >> simp[PULL_EXISTS] >>
  qexists_tac ‘(postcloudR sim sR tR)ᵀ’ >> simp[] >> conj_tac
  >- simp[RSUBSET,postcloudR_def] >>
  simp[forward_sim_def, postcloudR_def] >>
  qexists_tac ‘tterm sim sR tR’ >> rw[]

    [‘postcloudR sim sR tR t0 s0’, ‘tR t0 t1’]
  >- (gs[postcloudR_def]
      >- (rename [‘tterm sim sR tR t1 t0’, ‘tR t0 t1’, ‘sim s0 t0’] >>





*)
*)
val _ = export_theory();
