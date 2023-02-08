open preamble choreoUtilsTheory chorLangTheory chorLangPropsTheory
     itreeTauTheory iforestTheory itreeCommonTheory itreePropsTheory
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
val itree_thms = [ dsubst_def,project_def
                 , chor_itree_merge_def
                 , nub'_APPEND
                 , nub'_dvarsOf
                 , nub'_def
                 , nub'_procsOf
                 , dvarsOf_def
                 , procsOf_def
                 , split_sel_def
                 , itree_el_def
                 , itree_eqn_def
                 , itree_eqn_refl
                 , itree_eqn_sym
                 , itree_depth_eqv_def
                 , chor_itree_def
                 , dsubst_def
                 , dprocsOf_def
                 , no_undefined_FLOOKUP
                 , nub'_dprocsOf]

val itree_simp = rw itree_thms \\ gs itree_thms

val iforest_thm = [ iforest_can_act_def
                  , iforest_itrees_def
                  , iforest_get_def
                  , iforest_set_def
                  , iforest_del_def
                  , iforest_step_def
                  , iforest_upd_def
                  , FLOOKUP_UPDATE
                  , chor_iforest_def
                  , chor_forest_def
                  , chor_itree_def
                  , libTheory.the_def
                  ] @ itree_thms

val iforest_simp = rw iforest_thm \\ gs iforest_thm

Triviality project_split_eq:
  ∀ c c' p dvars.
    project' p dvars c = project' p dvars c' ∧
    project_ok p dvars c = project_ok p dvars c' ⇒
    project p dvars c = project p dvars c'
Proof
  rw[] \\ qmatch_goalsub_abbrev_tac ‘a = b’
  \\ Cases_on ‘a’ \\ Cases_on ‘b’
  \\ gs[]
QED

Theorem no_undefined_vars_simps:
  (∀s p x q y c.
     no_undefined_vars (s, Com p x q y c) ⇒
     no_undefined_vars (s |+ ((y,q),THE(FLOOKUP s (x,p))), c)) ∧
  (∀s p b q c.
     no_undefined_vars (s, Sel p b q c) ⇒ no_undefined_vars (s,c)) ∧
  (∀s p v c1 c2.
     no_undefined_vars (s, IfThen v p c1 c2) ⇒
     no_undefined_vars (s, c1) ∧ no_undefined_vars (s, c2))
Proof
  rw[no_undefined_vars_def,free_variables_def,SUBSET_INSERT_DELETE]
QED

Theorem no_undefined_vars_com = CONJUNCTS no_undefined_vars_simps |> el 1
Theorem no_undefined_vars_sel = CONJUNCTS no_undefined_vars_simps |> el 2
Theorem no_undefined_vars_if  = CONJUNCTS no_undefined_vars_simps |> el 3

Theorem rooted_step:
  ∀ψ p q.
    iforest_can_act ψ q ∧ rooted (iforest_step ψ q) p ⇒ rooted ψ p
Proof
  rw[] \\ Cases_on ‘iforest_can_act ψ p’
  \\ metis_tac[rooted_rules]
QED

Theorem chor_forest_st_idem:
  ∀c s p x v l.
    ¬ MEM p l ⇒
    chor_forest c (s |+ ((x,p),v)) l = chor_forest c s l
Proof
  rw[] \\ Induct_on ‘l’ \\ rw[chor_forest_def]
  \\ first_x_assum drule \\ rw[projectS_def]
QED

Theorem chor_forest_com_idem:
  ∀c s p q x y l.
  ¬ MEM p l ∧ ¬ MEM q l
  ⇒ chor_forest (Com p x q y c) s l = chor_forest c s l
Proof
  rw[] \\ Induct_on ‘l’ \\ rw[chor_forest_def]
  \\ first_x_assum (drule_then drule) \\ rw[]
  \\ rw[chor_itree_def]
QED

Theorem chor_forest_FUPDATE:
  ∀c s l p it.
    chor_forest c s l |+ (p,it) = chor_forest c s (FILTER (λy. p ≠ y) l) |+ (p,it)
Proof
  rw [] \\ Induct_on ‘l’ \\ rw[chor_forest_def]
  >- metis_tac [FUPDATE_COMMUTES]
  \\ rw[FUPDATE_EQ]
QED

Theorem chor_forest_FDOM:
  ∀c s l.
    FDOM (chor_forest c s l) = set l
Proof
  rw [] \\ Induct_on ‘l’ \\ rw[chor_forest_def]
QED


Theorem MEM_procsOf_chor_itree:
  ∀c p s. ¬ MEM p (procsOf c) ∧ dvarsOf c = [] ⇒ chor_itree p s c = Ret End
Proof
  rw[] \\ Induct_on ‘c’ \\ itree_simp \\ gs[MEM_FILTER,chor_itree_merge_def]
QED

Theorem chor_iforest_all_rooted:
  ∀c st.
    dvarsOf c = [] ∧
    no_undefined_vars (st,c) ∧
    no_self_comunication c
    ⇒ all_rooted (chor_iforest c st)
Proof
  simp[all_rooted_def,chor_iforest_itrees_eq_procOf]
  \\ Induct \\ rw[]
  (* Nil *)
  >- iforest_simp
  (* If *)
  >- (drule chor_iforest_split \\ disch_then (ONCE_REWRITE_TAC o single)
      \\ gs[procsOf_def,nub'_def,nub'_procsOf,nub'_APPEND] \\ rveq
      >- (irule rooted_can_act
          \\ drule no_undefined_FLOOKUP_if
          \\ iforest_simp)
      >- (drule (MEM_FILTER |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL) \\ rw[]
          \\ iforest_simp \\ cheat)
      >- cheat)
  (* Com *)
  >- (rw iforest_thm
      >-(gs[procsOf_def,nub'_def] \\ rveq
         >-(irule rooted_can_act \\ iforest_simp)
         >-(irule rooted_one_step
            \\ conj_tac >- iforest_simp
            \\ qexists_tac ‘s2’
            \\ iforest_simp
            \\ irule rooted_can_act
            \\ iforest_simp)
         >- (irule rooted_step
             \\ qexists_tac ‘s2’
             \\ conj_tac >- iforest_simp
             \\ rw iforest_thm
             \\ irule rooted_step
             \\ qexists_tac ‘s0’
             \\ conj_tac >- iforest_simp
             \\ rw iforest_thm
             \\ drule no_undefined_vars_com \\ strip_tac
             \\ gs[dvarsOf_def,nub'_dvarsOf]
             \\ first_x_assum drule
             \\ disch_then (qspec_then ‘p’ mp_tac)
             \\ impl_tac
             >- gs[MEM_FILTER,nub'_procsOf,no_self_comunication_def]
             \\ Cases_on ‘MEM s0 (procsOf c)’
             \\ Cases_on ‘MEM s2 (procsOf c)’
             >- (dxrule chor_iforest_split \\ disch_then (ONCE_REWRITE_TAC o single)
                 \\ dxrule chor_iforest_split \\ disch_then (ONCE_REWRITE_TAC o single)
                 \\ iforest_simp \\ iforest_simp
                 \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [chor_forest_FUPDATE])
                 \\ gs [FILTER_FILTER,MEM_FILTER]
                 \\ gs [FUPDATE_COMMUTES]
                 \\ qpat_assum ‘s2 ≠ s0’ (assume_tac o GSYM)
                 \\ dxrule_then (fn t => pop_assum (assume_tac o ONCE_REWRITE_RULE [t])) FUPDATE_COMMUTES
                 \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [chor_forest_FUPDATE])
                 \\ gs[FILTER_FILTER]
                 \\ qmatch_asmsub_abbrev_tac ‘rooted a p’
                 \\ qmatch_goalsub_abbrev_tac ‘rooted b p’
                 \\ ‘b = a’ suffices_by simp []
                 \\ UNABBREV_ALL_TAC
                 \\ simp[iforest_component_equality]
                 \\ qmatch_goalsub_abbrev_tac ‘a1 |+ b1 |+ c1 = a2 |+ b2 |+ c2’
                 \\ ‘a1 = a2 ∧ b1 = b2 ∧ c1 = c2’ suffices_by simp[]
                 \\ UNABBREV_ALL_TAC \\ rw[]
                 >- (rw [chor_forest_com_idem,chor_forest_st_idem,MEM_FILTER]
                     \\ AP_TERM_TAC
                     \\ rw [FILTER_EQ]
                     \\ metis_tac [])
                 >- rw[projectS_def]
                 >- metis_tac[projectS_fupdate,no_undefined_FLOOKUP_com,lookup_projectS])
             >- (gs[FUPDATE_COMMUTES]
                 \\ dxrule chor_iforest_split \\ disch_then (ONCE_REWRITE_TAC o single)
                 \\ iforest_simp
                 \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [chor_forest_FUPDATE])
                 \\ drule MEM_procsOf_chor_itree \\ rw[]
                 \\ irule rooted_step
                 \\ qexists_tac ‘s2’
                 \\ conj_tac >- iforest_simp
                 \\ iforest_simp
                 \\ gs [FILTER_FILTER,MEM_FILTER,DOMSUB_FUPDATE_NEQ]
                 \\ qmatch_asmsub_abbrev_tac ‘rooted a p’
                 \\ qmatch_goalsub_abbrev_tac ‘rooted b p’
                 \\ ‘b = a’ suffices_by simp []
                 \\ UNABBREV_ALL_TAC
                 \\ simp[iforest_component_equality]
                 \\ qmatch_goalsub_abbrev_tac ‘a1 |+ b1 = a2 |+ b2’
                 \\ ‘a1 = a2 ∧ b1 = b2’ suffices_by simp[]
                 \\ UNABBREV_ALL_TAC \\ rw[]
                 >- (rw [chor_forest_com_idem,chor_forest_st_idem,MEM_FILTER]
                     \\ irule EQ_TRANS \\ irule_at Any DOMSUB_NOT_IN_DOM
                     \\ rw[chor_forest_FDOM,MEM_FILTER]
                     \\ AP_TERM_TAC
                     \\ rw[FILTER_EQ] \\ metis_tac [])
                 >- (metis_tac[projectS_fupdate,no_undefined_FLOOKUP_com,lookup_projectS]))
             >- (gs[FUPDATE_COMMUTES]
                 \\ dxrule chor_iforest_split \\ disch_then (ONCE_REWRITE_TAC o single)
                 \\ iforest_simp
                 \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [chor_forest_FUPDATE])
                 \\ drule MEM_procsOf_chor_itree \\ rw[]
                 \\ irule rooted_step
                 \\ qexists_tac ‘s0’
                 \\ conj_tac >- iforest_simp
                 \\ iforest_simp
                 \\ gs [FILTER_FILTER,MEM_FILTER,DOMSUB_FUPDATE_NEQ]
                 \\ qmatch_asmsub_abbrev_tac ‘rooted a p’
                 \\ qmatch_goalsub_abbrev_tac ‘rooted b p’
                 \\ ‘b = a’ suffices_by simp []
                 \\ UNABBREV_ALL_TAC
                 \\ simp[iforest_component_equality]
                 \\ qmatch_goalsub_abbrev_tac ‘a1 |+ b1 = a2 |+ b2’
                 \\ ‘a1 = a2 ∧ b1 = b2’ suffices_by simp[]
                 \\ UNABBREV_ALL_TAC \\ rw[]
                 >- (rw [chor_forest_com_idem,chor_forest_st_idem,MEM_FILTER]
                     \\ irule EQ_TRANS \\ irule_at Any DOMSUB_NOT_IN_DOM
                     \\ rw[chor_forest_FDOM,MEM_FILTER]
                     \\ AP_TERM_TAC
                     \\ rw[FILTER_EQ] \\ metis_tac [])
                 >- rw[projectS_def])
             >- (gs[FUPDATE_COMMUTES]
                 \\ qpat_assum ‘¬MEM s0 _’ (mp_then Any mp_tac MEM_procsOf_chor_itree)
                 \\ disch_then (simp o single)
                 \\ qpat_assum ‘¬MEM s2 _’ (mp_then Any mp_tac MEM_procsOf_chor_itree)
                 \\ disch_then (simp o single)
                 \\ rw[]
                 \\ irule rooted_step
                 \\ qexists_tac ‘s0’
                 \\ iforest_simp
                 \\ gs [DOMSUB_FUPDATE_NEQ]
                 \\ irule rooted_step
                 \\ qexists_tac ‘s2’
                 \\ iforest_simp
                 \\ gs [FILTER_FILTER,MEM_FILTER]
                 \\ qmatch_asmsub_abbrev_tac ‘rooted a p’
                 \\ qmatch_goalsub_abbrev_tac ‘rooted b p’
                 \\ ‘b = a’ suffices_by simp []
                 \\ UNABBREV_ALL_TAC
                 \\ simp[iforest_component_equality]
                 \\ rw [chor_forest_com_idem,chor_forest_st_idem,MEM_FILTER]
                 \\ irule EQ_TRANS \\ irule_at Any DOMSUB_NOT_IN_DOM
                 \\ rw[chor_forest_FDOM,MEM_FILTER]
                 \\ irule EQ_TRANS \\ irule_at Any DOMSUB_NOT_IN_DOM
                 \\ rw[chor_forest_FDOM,MEM_FILTER]
                 \\ AP_TERM_TAC
                 \\ rw[FILTER_EQ_ID,EVERY_MEM]
                 \\ CCONTR_TAC \\ gs[])))
      >- (drule no_undefined_FLOOKUP_com \\ rw[]
          \\ drule lookup_projectS \\ gs[])
      >- gs[no_self_comunication_def]
      >- (drule no_undefined_FLOOKUP_com \\ rw[]
          \\ drule lookup_projectS \\ gs[]))
  \\ cheat
QED

Inductive from_chor_forest:
[~init:]
  (∀c s. from_chor_forest c (chor_iforest c s)) ∧
[~step:]
  (∀c p.
      from_chor_forest c ψ ⇒
      from_chor_forest c (iforest_step ψ p))
End

Inductive to_chor_forest:
[~init:]
  (∀c s. to_chor_forest c (chor_iforest c s)) ∧
[~step:]
  (∀c p.
     MEM p (procsOf c) ∧ iforest_can_act ψ p ∧
     (∀p. p ∈ iforest_itrees ψ ⇒ to_chor_forest c (iforest_step ψ p)) ⇒
     to_chor_forest c ψ)
End

Theorem iforest_step_to_chor_forest:
  ∀c s p.
    MEM p (procsOf c) ⇒
    to_chor_forest c (iforest_step (chor_iforest c s) p)
Proof
  cheat
QED

Theorem iforest_step_preserves_to_chor_forest:
  ∀c ψ. to_chor_forest c ψ ⇒ to_chor_forest c (iforest_step ψ p)
Proof
  rw[]
  \\ first_assum mp_tac
  \\ simp_tac std_ss [Once to_chor_forest_cases] \\ reverse (rw[])
  >- (Cases_on ‘p ∈ iforest_itrees ψ’
      >- metis_tac []
      >- (gs[iforest_itrees_def]
          \\ rw[iforest_step_def,iforest_get_def,FLOOKUP_DEF]))
  >- (Cases_on ‘p ∈ iforest_itrees (chor_iforest c s)’
      >- fs[iforest_step_to_chor_forest,chor_iforest_itrees_eq_procOf]
      >- (iforest_simp \\ simp[FLOOKUP_DEF]))
QED

Theorem iforest_steps_IMP_Res:
  ∀f s res.
    iforest_steps f s res ⇒
    ∀c p.
      set (procsOf c) ⊆ s ∧ to_chor_forest c f ∧ MEM p (procsOf c) ⇒
      EXISTS (λ(q,a). p = q ∧ ∃t. a = Res t) res
Proof
  Induct_on ‘iforest_steps’ \\ rpt strip_tac
  >- (gvs [SUBSET_DEF]
      \\ fs [Once to_chor_forest_cases]
      >- metis_tac [iforest_can_act_exists]
      \\ metis_tac [])
  \\ gvs []
  \\ rewrite_tac [METIS_PROVE [] “b ∨ c ⇔ ~b ⇒ c”]
  \\ strip_tac
  \\ first_x_assum irule
  \\ irule_at Any SUBSET_TRANS
  \\ first_x_assum $ irule_at $ Pos $ el 2
  \\ irule_at Any iforest_step_preserves_to_chor_forest
  \\ first_x_assum $ irule_at $ Pos hd \\ fs []
QED

Theorem chor_iforest_deadlock_freedom:
  ∀procs c s.
    fair_trace (set (procsOf c)) procs
    ⇒ deadlock_freedom (set (procsOf c)) (iforest (chor_iforest c s) procs)
Proof
  simp [deadlock_freedom_def]
  \\ rpt gen_tac \\ strip_tac
  \\ conj_asm1_tac
  >- cheat (* actions_end (iforest (chor_iforest ...)) *)
  \\ CCONTR_TAC \\ fs []
  \\ drule_all LFINITE_iforest
  \\ strip_tac \\ fs [exists_fromList]
  \\ drule iforest_steps_IMP_Res \\ simp []
  \\ irule_at Any to_chor_forest_init
  \\ first_x_assum $ irule_at Any \\ fs []
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
