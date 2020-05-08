open preamble chor_to_pchorTheory congProofTheory
open chorLangTheory chorSemTheory chorPropsTheory
open pchorLangTheory pchorSemTheory
open chorConfluenceTheory chorSyncPropsTheory choreoUtilsTheory

val _ = new_theory "chor_to_pchorProof"

Definition ptag_def:
  ptag (chorSem$LTau p n)      = (pchorSem$LTau p n)
∧ ptag (chorSem$LCom p v q x)  = (pchorSem$LCom p v q x)
∧ ptag (chorSem$LSel p b q)    = (pchorSem$LSel p b q)
∧ ptag (chorSem$LLet v p f vl) = (pchorSem$LLet v p f vl)
End

Theorem freeprocs_p_eq:
  ∀τ. freeprocs τ = freeprocs (ptag τ)
Proof
  Cases
  \\ fs [pchorSemTheory.freeprocs_def,
         chorSemTheory.freeprocs_def,
         ptag_def]
QED

Theorem project_inj:
  ∀p q. project p = project q ⇒ p = q
Proof
  Induct \\ rw [project_def]
  \\ Cases_on ‘q’ \\ fs [project_def]
QED

Theorem sync_trans_ptrans:
  ∀s c τ s' c'.
   trans (s,c) (τ,[]) (s',c')
   ⇒ ptrans (s,project c) (ptag τ) (s',project c')
Proof
  ‘∀s c τ l s' c'.
   trans (s,c) (τ,l) (s',c')
   ⇒ l = []
     ⇒ ptrans (s,project c) (ptag τ) (s',project c')’
  suffices_by metis_tac []
  \\ ho_match_mp_tac trans_pairind
  \\ rw [project_def,
         ptag_def,
         ptrans_rules,
         freeprocs_p_eq]
  \\ fs [lcong_nil_simp,freeprocs_p_eq,ptrans_rules]
QED

Theorem ptrans_sync_trans:
  ∀s c τ s' c'.
   ptrans (s,project c) (ptag τ) (s',project c')
   ⇒ trans (s,c) (τ,[]) (s',c')
Proof
  ‘∀s p γ s' q.
   ptrans (s,p) γ (s',q)
   ⇒ ∀c τ c'. γ = (ptag τ) ∧ p = (project c) ∧ q = (project c')
     ⇒ trans (s,c) (τ,[]) (s',c')’
  suffices_by metis_tac []
  \\ ho_match_mp_tac ptrans_pairind
  \\ rw [project_def,
         ptag_def,
         trans_rules,
         freeprocs_p_eq]
  \\ fs [lcong_nil_simp,freeprocs_p_eq,trans_rules]
  (* First 9 goals *)
  \\ TRY (Cases_on ‘τ’ \\ fs [ptag_def] \\ rveq
          \\ Cases_on ‘c’ \\ fs [project_def]
          \\ drule_then assume_tac project_inj
          \\ rveq \\ fs [trans_rules] \\ NO_TAC)
  (* Swap cases *)
  \\ Cases_on ‘c’
  \\ Cases_on ‘c'’
  \\ fs [project_def] \\ rveq
  \\ (irule trans_if_swap  ORELSE
      irule trans_com_swap ORELSE
      irule trans_sel_swap ORELSE
      irule trans_let_swap)
  \\ fs [freeprocs_p_eq]
  \\ qexists_tac ‘[]’ \\ fs [lcong_sym]
QED

Theorem trans_sync_eq_ptrans_s:
  ∀s c s' c'.
   trans_sync (s,c) (s',c') ⇒ ptrans_s (s,project c) (s',project c')
Proof
  ‘∀p q. trans_sync p q
    ⇒ ∀s c s' c'. p = (s,c) ∧ q = (s',c')
       ⇒ ptrans_s (s,project c) (s',project c')’
  suffices_by metis_tac []
  \\ simp [trans_sync_def]
  \\ ho_match_mp_tac RTC_ind
  \\ rw [ptrans_s_def] \\ rw []
  \\ Cases_on ‘p'’ \\ fs []
  \\ drule_then assume_tac sync_trans_ptrans
  \\ fs [ptrans_s_def]
  \\ irule RTC_TRANS
  \\ metis_tac []
QED

Theorem preservation:
  ∀s c α τ s' c'.
   no_self_comunication c ∧
   no_undefined_vars (s,c) ∧
   trans (s,c) (α,τ) (s',c')
   ⇒ ∃c'' s''.
      trans_sync (s',c') (s'',c'') ∧
      ptrans_s (s,project c) (s'',project c'')
Proof
  rpt (strip_tac)
  \\ drule_then drule no_undefined_vars_trans_pres
  \\ drule_then drule no_self_comunication_trans_pres
  \\ disch_then (mp_then Any assume_tac trans_lSyncTrm)
  \\ first_x_assum (disch_then o (mp_then Any (qspec_then ‘LIST_TO_BAG τ’ assume_tac)))
  \\ Cases_on ‘lSyncTrm (s',c') (LIST_TO_BAG τ)’
  \\ asm_exists_tac
  \\ fs []
  \\ ho_match_mp_tac trans_sync_eq_ptrans_s
  \\ first_x_assum (assume_tac o GSYM) \\ fs []
  \\ first_x_assum (K ALL_TAC)
  \\ ho_match_mp_tac trans_lSyncTrm_chorTrm
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
QED

val _ = export_theory ()
