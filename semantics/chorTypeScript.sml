open HolKernel Parse boolLib bossLib richerLangTheory envSemTheory finite_mapTheory

open chorLangTheory

val _ = new_theory "chorType";


Inductive chorTypecheckOK:
[~nil:] ∀ Γ Θ. chorTypecheckOK Γ Θ Nil
[~com:] ∀ Γ Θ p1 v1 p2 v2 c. FLOOKUP Γ (v1,p1) = SOME strT ∧
                             ({p1;p2} ⊆ Θ) ∧ p1≠ p2 ∧
                             chorTypecheckOK (Γ |+ ((v2,p2), strT)) Θ c ⇒
                             chorTypecheckOK Γ Θ (Com p1 v1 p2 v2 c)
[~sel:] ∀ Γ Θ p1 p2 b c. ({p1;p2} ⊆ Θ) ∧ p1 ≠ p2 ∧ chorTypecheckOK Γ Θ c ⇒
                         chorTypecheckOK Γ Θ (Sel p1 b p2 c)
[~if:] ∀ Γ Θ v p c1 c2. FLOOKUP Γ (v,p) = SOME boolT ∧
                        chorTypecheckOK Γ Θ c1 ∧ chorTypecheckOK Γ Θ c2 ⇒
                        chorTypecheckOK Γ Θ (IfThen v p c1 c2)
[~let:] ∀ Γ Θ v p e c ety. typecheck (localise Γ p) e ety ∧
                           chorTypecheckOK (Γ |+ ((v,p), ety)) Θ c ⇒
                           chorTypecheckOK Γ Θ (Let v p e c)
[~fix:] ∀ Γ Θ c dn. chorTypecheckOK Γ (Θ ∪ {dn}) c ⇒ chorTypecheckOK Γ Θ (Fix dn c)
[~call:] ∀ Γ Θ dn. {dn} ⊆ Θ ⇒ chorTypecheckOK Γ Θ (Call dn)
End

Definition chorEnvtype_def:
  chorEnvtype Γ s = (∀ p. envtype (localise Γ p) (localise s p))
End

        
val _ = export_theory();

