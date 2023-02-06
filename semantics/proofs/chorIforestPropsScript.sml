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

Theorem iforest_step_chor_iforest:
  ∀c p s q.
    iforest_can_act (chor_iforest c s q) p ⇒
  ∃c' s' q'. set (procsOf c') ⊆ set(procsOf c) ∧
       iforest_step (chor_iforest c s q) p = chor_iforest c' s' q' ∧
       ∀p'. p' ∈ set(procsOf c) ∧
            (p = p' ⇒ ∀r. iforest_get (chor_iforest c s q) p ≠ SOME (Ret r)) ⇒
            p' ∈ set(procsOf c')
Proof
  cheat
QED

Theorem iforest_steps_IMP_Res:
  ∀f s res.
    iforest_steps f s res ⇒
    ∀c p st q.
      set(procsOf c) ⊆ s ∧ f = chor_iforest c st q ∧ p ∈ set (procsOf c) ⇒
      EXISTS (λ(q,a). p = q ∧ ∃t. a = Res t) res
Proof
  Induct_on ‘iforest_steps’ \\ rpt strip_tac
  >- (gvs [SUBSET_DEF] \\ metis_tac [iforest_can_act_exists])
  \\ gvs []
  \\ rewrite_tac [METIS_PROVE [] “b ∨ c ⇔ ~b ⇒ c”]
  \\ strip_tac
  \\ first_x_assum irule
  \\ irule_at Any SUBSET_TRANS
  \\ first_x_assum $ irule_at $ Pos $ el 2
  \\ drule iforest_step_chor_iforest
  \\ strip_tac
  \\ first_assum $ irule_at $ Pos hd \\ fs []
  \\ qexistsl_tac [‘s'’,‘q'’] \\ simp[]
  \\ pop_assum $ irule \\ fs []
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘iforest_act (chor_iforest c st q) p’ \\ fs []
  \\ fs [iforest_act_def, iforest_can_act_def]
  \\ Cases_on ‘iforest_get (chor_iforest c st q) p’ \\ fs []
  \\ Cases_on ‘x’ \\ gvs []
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

Theorem chor_iforest_all_rooted:
  ∀c st q.
    no_undefined_vars (st,c) ∧
    no_self_comunication c ∧
    compile_network_ok st c (procsOf c)
    ⇒ all_rooted (chor_iforest c st)
Proof
  simp[all_rooted_def,chor_iforest_itrees_eq_procOf]
  \\ Induct \\ rw[]
  (* Nil *)
  >- gs[procsOf_def]
  (* If *)
  >- (drule chor_iforest_split \\ disch_then (ONCE_REWRITE_TAC o single)
     \\ gs[procsOf_def,nub'_def,nub'_procsOf,nub'_APPEND] \\ rveq
      >- (irule rooted_can_act
          \\ drule no_undefined_FLOOKUP_if
          \\ rw[no_undefined_FLOOKUP_if,FLOOKUP_UPDATE
                ,iforest_can_act_def,iforest_get_def,iforest_set_def
                ,chor_iforest_def,chor_forest_def,chor_itree_def
                ,procsOf_def,nub'_def,nub'_procsOf,nub'_APPEND])
      \\ cheat)
  \\ cheat
QED

Theorem chor_iforest_deadlock_freedom:
  ∀procs c s.
    fair_trace (set (procsOf c)) procs
    ⇒ deadlock_freedom (set (procsOf c)) (iforest (chor_iforest c s) procs)
Proof
  simp [deadlock_freedom_def]
  \\ rpt gen_tac \\ strip_tac
  \\ conj_asm1_tac
  >- simp[actions_end_iforest]
  \\ CCONTR_TAC \\ fs []
  \\ drule_all LFINITE_iforest
  \\ strip_tac \\ fs [exists_fromList]
  \\ gvs [o_DEF,LAMBDA_PROD,LFINITE_fromList]
  \\ qpat_x_assum ‘_ = fromList res’ kall_tac
  \\ last_x_assum kall_tac
  \\ drule iforest_steps_IMP_Res
  \\ disch_then $ drule_at $ Pos last
  \\ gvs [o_DEF,LAMBDA_PROD,LFINITE_fromList]
  \\ metis_tac []
QED

val _ = export_theory ()
