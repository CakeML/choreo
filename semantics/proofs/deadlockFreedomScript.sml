open preamble choreoUtilsTheory chorSemTheory chorPropsTheory

val _ = new_theory "deadlockFreedom";

Theorem chor_deadlock_freedom:
  ∀c s.
   no_undefined_vars (s,c) ∧
   no_self_comunication c
   ⇒ ∃s'. trans_s (s,c) (s',Nil)
Proof
  Induct
  \\ rw [] \\ rw []
  (* Nil *)
  >- (qexists_tac `s` \\ rw [trans_s_def])
  (* IfThen *)
  >- (`no_undefined_vars (s',c)  ∧
       no_undefined_vars (s',c') ∧
       no_self_comunication c    ∧
       no_self_comunication c'`
       by fs [no_undefined_vars_def,free_variables_def,no_self_comunication_def]
     \\ first_x_assum drule \\ disch_then drule
     \\ first_x_assum drule \\ disch_then drule
     \\ rw []
     \\ rename1 ‘IfThen v’
     \\ Cases_on `FLOOKUP s' (v,s) = SOME [1w]`
     >- (qexists_tac `s''`
        \\ fs [trans_s_def]
        \\ ho_match_mp_tac RTC_TRANS
        \\ metis_tac [trans_if_true])
     \\ Cases_on `FLOOKUP s' (v,s) = NONE`
     >- fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
     \\ qexists_tac `s'''`
     \\ `∃d. FLOOKUP s' (v,s) = SOME d ∧ d ≠ [1w]`
        by (Cases_on `FLOOKUP s' (v,s)` \\ fs [])
     \\ fs [trans_s_def]
     \\ ho_match_mp_tac RTC_TRANS
     \\ metis_tac [trans_rules])
  (* Communication *)
  >- (rename1 ‘Com p1 v1 p2 v2’
     \\ `∃d. FLOOKUP s' (v1,p1) = SOME d`
        by fs [no_undefined_vars_def,free_variables_def,FLOOKUP_DEF]
     \\ `no_undefined_vars (s' |+ ((v2,p2),d),c) ∧ no_self_comunication c`
        by fs [no_undefined_vars_def,free_variables_def
              , no_self_comunication_def
              , DELETE_SUBSET_INSERT]
     \\ first_x_assum drule \\ disch_then drule
     \\ rw [] \\ fs [no_self_comunication_def]
     \\ qexists_tac `s''`
     \\ fs [trans_s_def]
     \\ ho_match_mp_tac RTC_TRANS
     \\ metis_tac [trans_com])
  (* Let *)
  >- (rename1 ‘Let v p f’
      \\ `no_undefined_vars (s' |+ ((v,p), f (MAP (THE ∘ FLOOKUP s')
                                              (MAP (λv. (v,p)) l))), c) ∧
          no_self_comunication c`
       by fs [no_undefined_vars_def
             , free_variables_def
             , no_self_comunication_def
             , DELETE_SUBSET_INSERT]
      \\ first_x_assum drule \\ disch_then drule \\ rw []
      \\ `EVERY IS_SOME (MAP (FLOOKUP s') (MAP (λv. (v,p)) l))`
         by (last_assum mp_tac \\  rpt (pop_assum (K ALL_TAC))
            \\ rw [no_undefined_vars_def,free_variables_def]
            \\ Induct_on `l` \\ rw [IS_SOME_EXISTS,FLOOKUP_DEF])
      \\ qexists_tac `s''`
      \\ fs [trans_s_def]
      \\ ho_match_mp_tac RTC_TRANS
      \\ metis_tac [trans_let])
  (* Selection *)
  >- (`no_undefined_vars (s',c) ∧ no_self_comunication c`
        by fs [no_undefined_vars_def,free_variables_def
               , no_self_comunication_def
               , DELETE_SUBSET_INSERT]
      \\ first_x_assum drule \\ disch_then drule \\ rw []
      \\ qexists_tac `s''`
      \\ fs [trans_s_def,no_self_comunication_def]
      \\ ho_match_mp_tac RTC_TRANS
      \\ metis_tac [trans_sel])
QED

val _ = export_theory ()
