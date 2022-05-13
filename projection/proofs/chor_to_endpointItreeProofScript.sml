open preamble

open itreesTheory itreeCommonTheory
open chorLangTheory chorItreeSemTheory
open endpointLangTheory endpointItreeSemTheory
open chor_to_endpointTheory


val _ = new_theory "chor_to_endpointItreeProof";

Theorem chor_to_endpoint_itree_eq:
  ∀p dvars c s.
    project_ok p dvars c ⇒
    chor_itree p s c = endpoint_itree s (project' p dvars c)
Proof
  ho_match_mp_tac project_ind
  \\ rw[project_def,chor_itree_def,endpoint_itree_def]
  >- (IF_CASES_TAC \\ simp[FUN_EQ_THM]
      \\ Cases \\ rw[])
  >- (simp[FUN_EQ_THM]
      \\ Cases \\ rw[])
  >- cheat
  >- cheat
  >- (simp[FUN_EQ_THM]
      \\ Cases \\ rw[])
  >- (simp[FUN_EQ_THM]
      \\ Cases
      \\ rw[EPDONE,endpoint_itree_def])
  >-(simp[FUN_EQ_THM]
      \\ Cases
      \\ rw[EPDONE,endpoint_itree_def])
  \\ cheat
QED

val _ = export_theory ()
