open preamble

open itreeTauTheory itreeCommonTheory choreoUtilsTheory
open chorLangTheory chorLangPropsTheory chorItreeSemTheory
open endpointLangTheory endpointItreeSemTheory
open chor_to_endpointTheory chor_to_endpointPropsTheory

val _ = new_theory "chor_to_endpointItreeProof";

val itree_thms = [ dsubst_def,project_def
                 , chor_itree_merge_def
                 , nub'_APPEND
                 , nub'_dvarsOf
                 , dvarsOf_def
                 , procsOf_def
                 , split_sel_def
                 , itree_el_def
                 , itree_eqn_def
                 , itree_eqn_refl
                 , itree_eqn_sym
                 , itree_depth_eqv_def
                 , chor_itree_def
                 , endpoint_itree_def
                 , chorLangTheory.dsubst_def
                 , endpointLangTheory.dsubst_def
                 , dprocsOf_def
                 , nub'_dprocsOf]

val itree_simp = rw itree_thms \\ gs itree_thms

Theorem project_Nil_itree_End:
  ∀p dvars c s.
    dvarsOf c = [] ∧
    project p dvars c = (T,Nil)
    ⇒ chor_itree p s c = Ret End
Proof
  ho_match_mp_tac project_ind \\ itree_simp
  >- (gs[CaseEq"option",CaseEq"prod",CaseEq"bool"] \\ itree_simp)
  >- (gs[CaseEq"option",CaseEq"prod",CaseEq"bool"] \\ itree_simp)
  >- (gs[dprocsOf_dvarsOf_empty_cons,dvarsOf_def,nub'_dvarsOf,dprocsOf_empty])
QED

Theorem itree_eqn_merge:
  ∀n l r.
    itree_eqn n (↑ l) (↑ r)
    ⇒ itree_eqn n (↑ (chor_itree_merge l r)) (↑ l)
Proof
  Induct_on ‘n’ \\ rw[itree_eqn_def]
  \\ Cases_on ‘l’ \\ Cases_on ‘r’ \\ itree_simp
  \\ TRY (Cases_on ‘x’) \\ itree_simp
  \\ TRY (Cases_on ‘x'’) \\ itree_simp
QED

Definition closed_dvars:
  closed_dvars dvars c =
    (∀dn procs.
       ALOOKUP dvars dn = SOME procs ⇒ set procs ⊆ set (procsOf c))
End

Theorem dvarsOf_dsubst:
∀c fn c'.
  dvarsOf (Fix fn c) = [] ∧
  dvarsOf c' = []
  ⇒ dvarsOf (dsubst c fn c') = []
Proof
  rw[]
  \\ drule set_dvarsOf_dsubst_eq
  \\ disch_then (qspecl_then [‘c’,‘fn’] assume_tac)
  \\ gs[dvarsOf_def,nub'_dvarsOf]
  \\ mp_tac list_to_set_diff
  \\ qspecl_then [‘[fn]’,‘dvarsOf c’] assume_tac list_to_set_diff
  \\ gs[] \\ pop_assum kall_tac
  \\ qmatch_asmsub_abbrev_tac ‘FILTER l vars = []’
  \\ qmatch_asmsub_abbrev_tac ‘set (FILTER r vars)’
  \\ ‘FILTER r vars = FILTER l vars’ by
    (UNABBREV_ALL_TAC \\ gs[FILTER_EQ] \\ metis_tac [])
  \\ gs[]
QED

Theorem chor_to_endpoint_itree_eq:
  ∀p dvars c s.
    dvarsOf c = [] ∧
    project_ok p dvars c
    ⇒
    ↑(chor_itree p s c) = endpoint_itree s (project' p dvars c)
Proof
  let
      val split_cases = itree_simp
                        \\ Cases_on ‘split_sel p s' c’
                        \\ Cases_on ‘split_sel p s' c'’
                        \\ TRY (Cases_on ‘x’)
                        \\ TRY (Cases_on ‘x'’)
                        \\ rw[] \\ gs[]
      val base_cases =  itree_simp \\ Cases_on ‘a’ \\ itree_simp
      val split_NONE_case = metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge]
      val split_SOME_case = Induct_on ‘c’ \\ Induct_on ‘c'’ \\ itree_simp
                            \\ IF_CASES_TAC \\ itree_simp
                            \\ Cases_on ‘a’
                            \\ itree_simp
                            \\ TRY (first_x_assum
                                    (qspec_then ‘Branch T’
                                     (fn t => assume_tac t \\ itree_simp \\ NO_TAC))
                                    \\ NO_TAC)
                            \\ TRY (first_x_assum
                                    (qspec_then ‘Branch F’
                                     (fn t => assume_tac t \\ itree_simp \\ NO_TAC))
                                    \\ NO_TAC)
  in
  simp[GSYM itree_depth_eqv_eq,itree_depth_eqv_def]
  \\ CONV_TAC (DEPTH_CONV RIGHT_IMP_FORALL_CONV)
  \\ Induct_on ‘n’
  \\ rw[itree_eqn_def]
  \\ Induct_on ‘c’
  >- itree_simp
  >- (itree_simp
      >- (split_cases >- split_NONE_case >- split_SOME_case)
      >- (split_cases >- split_NONE_case >- split_SOME_case)
      >- (split_cases >- split_NONE_case >- split_SOME_case)
      >- (split_cases \\ split_SOME_case)
      >- (split_cases \\ split_SOME_case)
      >- (split_cases \\ split_SOME_case))
  >- base_cases >- base_cases >- base_cases
  >- (rw[]
      \\ qspecl_then [‘p’,‘dvars’,‘Fix s' c’] mp_tac project_ALOOKUP_EQ_strong
      \\ simp[] \\ disch_then (qspec_then ‘[]’ assume_tac) \\ gs[]
      \\ ‘dprocsOf [] (Fix s' c) = procsOf c’
            by (ONCE_REWRITE_TAC [GSYM dprocsOf_empty]
                \\ simp[dprocsOf_def,nub'_dprocsOf]
                \\ irule dprocsOf_dvarsOf_empty_cons
                \\ simp[dvarsOf_def,nub'_dvarsOf])
      \\ reverse (Cases_on ‘MEM p (dprocsOf [] (Fix s' c))’)
      >- itree_simp
      \\ drule project'_dsubst_commute
      \\ disch_then drule
      \\ disch_then (qspec_then ‘c’ mp_tac)
      \\ impl_tac
      >- itree_simp
      \\ disch_then (assume_tac o GSYM)
      \\ itree_simp
      \\ irule itree_eqn_trans
      \\ first_x_assum (irule_at Any)
      \\ qexists_tac ‘[]’
      \\ simp[itree_eqn_refl]
      \\ irule dvarsOf_dsubst
      \\ itree_simp)
  >- itree_simp
end
QED

val _ = export_theory ()
