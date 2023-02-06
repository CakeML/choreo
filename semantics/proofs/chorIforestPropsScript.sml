open preamble choreoUtilsTheory chorLangTheory chorLangPropsTheory
     itreeTauTheory iforestTheory itreeCommonTheory
     chorItreeSemTheory chorIforestSemTheory

open chor_to_endpointTheory; (* Required for projectability criteria *)

val _ = new_theory "chorIforestProps";

Theorem chor_ifores_nil_imp_procsOf_nil:
  ∀c s trace.
    iforest (chor_iforest c s) trace = [||] ∧
    fair_trace (set (procsOf c)) trace ⇒
    procsOf c = []
Proof
  let fun chor_tac n t =
      ntac n (last_x_assum kall_tac)
      \\ gs[Once iforest_def,CaseEq"option",CaseEq"prod"]
      \\ gs[next_proc_def,CaseEq"llist"]
      \\ drule LDROP_WHILE_EQ_NIL \\ rw[]
      \\ gs[fair_trace_def,every_LNTH]
      \\ first_x_assum (qspec_then t assume_tac)
      \\ gs[procsOf_def,nub'_def,Once always_cases]
      \\ first_x_assum drule
      \\ rw[chor_iforest_def,chor_forest_def,chor_itree_def,
            iforest_can_act_def,iforest_get_def,
            procsOf_def,nub'_def,FLOOKUP_UPDATE]
  in
    Induct \\ rw[]
  >- rw[procsOf_def]
  >- chor_tac 2 ‘s’
  >- chor_tac 1 ‘s2’
  >- chor_tac 1 ‘s’
  >- chor_tac 1 ‘s0’
  >- (last_x_assum kall_tac
      \\ gs[Once iforest_def,CaseEq"option",CaseEq"prod"]
      \\ gs[next_proc_def,CaseEq"llist"]
      \\ drule LDROP_WHILE_EQ_NIL \\ rw[]
      \\ gs[fair_trace_def,every_LNTH]
      \\ last_x_assum kall_tac
      \\ gs[procsOf_def,nub'_procsOf]
      \\ Cases_on ‘procsOf c’ \\ simp[]
      \\ first_x_assum (qspec_then ‘h’ assume_tac)
      \\ gs[procsOf_def,nub'_def,Once always_cases] \\ rveq
      \\ first_x_assum drule
      \\ rw[chor_iforest_def,chor_forest_def,chor_itree_def,
            iforest_can_act_def,iforest_get_def,
            procsOf_def,nub'_def,FLOOKUP_UPDATE])
  >- rw[procsOf_def]
end
QED

Inductive iforest_steps:
  (∀ψ s.
    (∀p. p ∈ s ⇒ ¬iforest_can_act ψ p) ⇒
    iforest_steps ψ s []) ∧
  (∀ψ s p res.
    iforest_can_act ψ p ∧
    iforest_steps (iforest_step ψ p) s res ⇒
    iforest_steps ψ s (iforest_act ψ p::res))
End

Triviality LNTH_every:
  ∀n l p P.
    LNTH n l = SOME p ∧ every P l ⇒ P p
Proof
  Induct \\ Cases_on ‘l’ \\ fs [] \\ rw [] \\ fs [] \\ res_tac
QED

Theorem LFINITE_iforest:
  LFINITE (iforest f trace) ∧ fair_trace s trace ⇒
  ∃res.
    iforest f trace = fromList res ∧
    iforest_steps f s res
Proof
  strip_tac
  \\ dxrule LFINITE_IMP_fromList
  \\ strip_tac \\ fs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘s’
  \\ qid_spec_tac ‘trace’
  \\ qid_spec_tac ‘f’
  \\ qid_spec_tac ‘l’
  \\ Induct \\ rw []
  \\ simp [Once iforest_steps_cases]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [iforest_def] \\ fs [AllCaseEqs(),EXISTS_PROD]
  >-
   (gvs [next_proc_def,AllCaseEqs()] \\ rw []
    \\ dxrule iforestTheory.LDROP_WHILE_EQ_NIL
    \\ gvs [fair_trace_def] \\ rw [] \\ CCONTR_TAC \\ fs []
    \\ last_x_assum drule
    \\ once_rewrite_tac [llistTheory.always_cases]
    \\ once_rewrite_tac [llistTheory.always_cases]
    \\ CCONTR_TAC \\ gvs []
    \\ ‘every ($¬ ∘ iforest_can_act f) (h:::t)’ by fs []
    \\ drule_all LNTH_every
    \\ fs [])
  \\ strip_tac \\ fs []
  \\ imp_res_tac iforestTheory.next_proc_fair_trace
  \\ gvs [next_proc_def,AllCaseEqs()]
  \\ irule_at (Pos hd) (METIS_PROVE [] “T ⇒ x = x”) \\ fs []
  \\ last_x_assum $ irule_at Any
  \\ pop_assum $ irule_at Any
  \\ drule iforestTheory.LDROP_WHILE_EQ_CONS
  \\ strip_tac \\ gvs []
QED

Theorem exists_fromList:
  ∀xs P. exists P (fromList xs) = EXISTS P xs
Proof
  Induct \\ fs [fromList_def]
QED

Theorem iforest_can_act_exists:
  ∀c p s.
     p ∈ set(procsOf c) ⇒
     ∃p'. p' ∈ set(procsOf c) ∧ iforest_can_act (chor_iforest c s) p'
Proof
  let fun chor_tac t = qexists_tac t \\ simp[]
      \\ rw[ iforest_can_act_def,chor_iforest_def
           , iforest_get_def,chor_forest_def
           , procsOf_def,nub'_def,FLOOKUP_UPDATE,chor_itree_def]
  in
  Cases_on ‘c’ \\ rw[]
  >- gs[procsOf_def]
  >- chor_tac ‘s’
  >- chor_tac ‘s2’
  >- chor_tac ‘s’
  >- chor_tac ‘s0’
  >- (gs[procsOf_def,nub'_procsOf]
      \\ Cases_on ‘procsOf c'’
      \\ gs[]
      \\ chor_tac ‘h’)
  >- gs[procsOf_def]
  end
QED

Theorem chor_iforest_itrees_eq_procOf:
  ∀c st. iforest_itrees (chor_iforest c st) = set (procsOf c)
Proof
  rw[chor_iforest_def,iforest_itrees_def]
  \\ qmatch_goalsub_rename_tac ‘set ll’
  \\ Induct_on ‘ll’ \\ rw[chor_forest_def]
QED

val _ = Parse.add_infix("<ψ>",480,Parse.LEFT);

val _ = Parse.overload_on("<ψ>",``λifst pit. iforest_set ifst (FST pit) (SND pit)``);

Theorem chor_iforest_split:
  ∀c p st.
    MEM p (procsOf c) ⇒
        chor_iforest c st = chor_iforest c st <ψ> (p,chor_itree p (projectS p st) c)
Proof
  rw[chor_iforest_def,iforest_set_def] \\ qmatch_asmsub_rename_tac ‘MEM _ ll’
  \\ Induct_on ‘ll’ \\ rw[chor_forest_def] \\ rw[FUPDATE_EQ]
  \\ metis_tac [FUPDATE_COMMUTES]
QED

(* rooted_can_act *)
val chor_thms = [ dsubst_def,project_def
                  , chor_itree_merge_def
                  , nub'_APPEND
                  , nub'_dvarsOf
                  , dvarsOf_def
                  , procsOf_def
                  , split_sel_def
                  , chor_itree_def
                  , dsubst_def
                  , dprocsOf_def
                  , nub'_dprocsOf ]

val iforest_thm = [ iforest_can_act_def
                  , iforest_get_def
                  , iforest_set_def
                  , FLOOKUP_UPDATE
                  , chor_iforest_def
                  , chor_forest_def
                  , chor_itree_def
                  ]

val iforest_simp = rw iforest_thm \\ gs iforest_thm

val chor_simp = rw chor_thms \\ gs chor_thms

Theorem chor_iforest_all_rooted:
  ∀c st q.
    no_undefined_vars (st,c) ∧
    no_self_comunication c ∧
    compile_network_ok st c (procsOf c)
    ⇒ all_rooted (chor_iforest c st)
Proof
  let
      val split_cases = chor_simp
                        \\ Cases_on ‘split_sel p s c0’
                        \\ Cases_on ‘split_sel p s c'’
                        \\ TRY (Cases_on ‘x’)
                        \\ TRY (Cases_on ‘x'’)
                        \\ rw[] \\ gs[]
  in
  simp[all_rooted_def,chor_iforest_itrees_eq_procOf]
  \\ rw[compile_network_ok_project_ok]
  \\ first_x_assum drule
  \\ Cases_on ‘c’ \\ rw[]
  (* Nil *)
  >- chor_simp
  (* If *)
  >- (drule chor_iforest_split \\ disch_then (ONCE_REWRITE_TAC o single)
      \\ gs[procsOf_def,nub'_def,nub'_procsOf,nub'_APPEND] \\ rveq
      >- (irule rooted_can_act
          \\ drule no_undefined_FLOOKUP_if
          \\ iforest_simp)
      >- (drule (MEM_FILTER |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL) \\ rw[]
          \\ chor_simp
          \\ split_cases
          >- (FULL_CASE_TAC \\ gs[] \\ cheat)
          >- (FULL_CASE_TAC \\ gs[]
              \\ FULL_CASE_TAC \\ gs[]
              \\ cheat))
      >- cheat)
  \\ cheat
  end
QED

Theorem chor_iforest_always_rooted:
  ∀c st.
    no_undefined_vars (st,c) ∧
    no_self_comunication c ∧
    compile_network_ok st c (procsOf c) ⇒
    always_rooted (chor_iforest c st)
Proof
  rw[always_rooted_def]
  \\ cheat
QED

Theorem chor_iforest_deadlock_freedom:
  ∀procs c s.
    fair_trace (set (procsOf c)) procs
    ⇒ deadlock_freedom (set (procsOf c)) (iforest (chor_iforest c s) procs)
Proof
  rw[]
  \\ qspec_then ‘chor_iforest c s’ mp_tac always_rooted_deadlock_freedom'
  \\ REWRITE_TAC [chor_iforest_itrees_eq_procOf] \\ disch_then irule \\ simp[]
  \\ irule chor_iforest_always_rooted
  \\ cheat
QED

val _ = export_theory ()
