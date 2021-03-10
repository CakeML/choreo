open HolKernel Parse boolLib bossLib;

open relationTheory
val _ = new_theory "abstractCompilation";

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
  triR R e1 e2 ⇔ ∃e. R꙳ e1 e ∧ R꙳ e2 e
End

Theorem RTC_triR:
  R꙳ a b ⇒ triR R a b
Proof
  simp[triR_def] >> metis_tac[RTC_REFL]
QED

Theorem triR_one_step_each:
  R a0 a ∧ R b0 b ∧ triR R a b ⇒ triR R a0 b0
Proof
  simp[triR_def] >> metis_tac[RTC_RULES]
QED

Theorem triR_step1:
  R a0 a ∧ triR R a b ⇒ triR R a0 b
Proof
  simp[triR_def] >> metis_tac[RTC_RULES]
QED

Theorem triR_steps1:
  R꙳ a0 a ∧ triR R a b ⇒ triR R a0 b
Proof
  simp[triR_def] >> metis_tac[RTC_CASES_RTC_TWICE]
QED

Theorem triR_RTC_each:
  R꙳ a0 a ∧ R꙳ b0 b ∧ triR R a b ⇒ triR R a0 b0
Proof
 metis_tac[triR_def, RTC_CASES_RTC_TWICE]
QED

Theorem triR_REFL[simp]:
  ∀x. triR R x x
Proof
  gen_tac >> simp[triR_def] >> irule_at Any RTC_REFL
QED

Theorem triR_SYM:
  ∀x y. triR R x y = triR R y x
Proof
  simp[triR_def] >> metis_tac[]
QED


Theorem triR_forward_simulation_has_all_terminations:
  simulates simR sR (triR tR) ∧ CR tR ∧
  (∀s t. nf sR s ∧ simR s t ⇒ ∃tt. nf tR tt ∧ tR꙳ t tt ∧ simR s tt) ⇒
  ∀s0 s t0.
    sR꙳ s0 s ∧ nf sR s ∧ simR s0 t0 ⇒
    ∃t.
      tR꙳ t0 t ∧ nf tR t ∧ simR s t
Proof
  strip_tac >> Induct_on ‘RTC’ >> rpt strip_tac
  >- metis_tac[] >>
  gs[simulates_def, triR_def] >> rename [‘nf sR s’, ‘sR s0 s0'’] >>
  ‘∃t tT. tR꙳ t0 tT ∧ simR s0' t ∧ tR꙳ t tT’ by metis_tac[] >>
  ‘∃tt. tR꙳ t tt ∧ simR s tt ∧ nf tR tt’ by metis_tac[] >>
  ‘∃d. tR꙳ tT d ∧ tR꙳ tt d’ by metis_tac[CR_def, diamond_def] >>
  qexists_tac ‘tt’ >> simp[] >>
  ‘tt = d’ by metis_tac[RTC_CASES1, nf_def] >>
  metis_tac[RTC_CASES_RTC_TWICE]
QED




val _ = export_theory();
