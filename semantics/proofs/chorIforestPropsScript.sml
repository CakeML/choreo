open preamble choreoUtilsTheory chorLangTheory chorLangPropsTheory
     itreeTauTheory iforestTheory itreeCommonTheory
     chorItreeSemTheory chorIforestSemTheory

val _ = new_theory "chorIforestProps";

Theorem chor_ifores_nil_imp_procsOf_nil:
  ∀c s q trace.
    iforest (chor_iforest c s q) trace = [||] ∧
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

val _ = export_theory ()
