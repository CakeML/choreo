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
  (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2) ∧
  (∀s0 t. tR (compile s0) t ⇒ ∃s. sR s0 s)
     (* alternatively: if s0 is a normal form, so too is compile s0 *)
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
  (∀t0 t1 t2. tR t0 t1 ∧ tR t0 t2 ⇒ t1 = t2) ∧
  (∀s0 t. tR (compile s0) t ⇒ ∃s. sR s0 s)
     (* alternatively: if s0 is a normal form, so too is compile s0 *)
  ⇒
  simulates (postcloud compile sR tR)ᵀ tR (RC sR)
Proof
  simp[simulates_def] >> metis_tac[forward_implies_back]
QED

val _ = export_theory();
