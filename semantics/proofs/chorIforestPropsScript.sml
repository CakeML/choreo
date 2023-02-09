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

Triviality LNTH_every:
  ∀n l p P.
    LNTH n l = SOME p ∧ every P l ⇒ P p
Proof
  Induct \\ Cases_on ‘l’ \\ fs [] \\ rw [] \\ fs [] \\ res_tac
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
fun iforest_tac t = rw (iforest_thm @ t) \\ gs (iforest_thm @ t)

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

Theorem iforest_step_update:
  p ≠ q ⇒
  iforest_step (f with forest := f.forest |+ (p,i)) q =
  iforest_step f q with forest := (iforest_step f q).forest |+ (p,i)
Proof
  iforest_simp >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  rw[iforest_component_equality,fmap_eq_flookup,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE] >>
  rw[]
QED

Theorem rooted_Vis_switch_cont:
  ∀f p a g h.
  rooted f p ∧
  FLOOKUP f.forest p = SOME(Vis a g)
  ⇒
  rooted (f with forest := f.forest |+ (p,Vis a h)) p
Proof
  Induct_on ‘rooted’ >>
  rw[]
  >- (match_mp_tac rooted_can_act >>
      iforest_simp)
  >- (‘p ≠ q’ by metis_tac[] >>
      match_mp_tac rooted_one_step >>
      qexists_tac ‘q’ >>
      conj_tac >- iforest_simp >>
      conj_tac >- iforest_simp >>
      simp[iforest_step_update] >>
      first_x_assum match_mp_tac >>
      qexists_tac ‘g’ >>
      iforest_simp >>
      rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
      simp[DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE])
QED

Theorem rooted_merge:
  ∀t1 t2 f p g h.
   FLOOKUP f.forest p = SOME(chor_itree_merge t1 t2) ∧
   rooted (f with forest := f.forest |+ (p,t1)) p ∧
   rooted (f with forest := f.forest |+ (p,t2)) p
   ⇒
   rooted f p
Proof
  Cases
  >- (rename1 ‘Ret x’ >> Cases_on ‘x’ >>
      Cases
      >- (rename1 ‘Ret x’ >> Cases_on ‘x’ >>
          rw[chor_itree_merge_def] >>
          match_mp_tac rooted_can_act >>
          iforest_simp) >>
      rw[chor_itree_merge_def]
      >~ [‘FLOOKUP _.forest _ = SOME (Vis _ _)’]
      >- (pop_assum mp_tac >>
          match_mp_tac(DECIDE “(A = B) ⇒ (A ⇒ B)”) >>
          rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
          rw[iforest_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE] >>
          rw[] >> rw[])
      >~ [‘FLOOKUP _.forest _ = SOME (chor_itree_merge _ _)’]
      >- (Cases_on ‘x’ >> gvs[chor_itree_merge_def] >>
          match_mp_tac rooted_can_act >>
          iforest_simp) >>
      match_mp_tac rooted_can_act >>
      iforest_simp)
  >- (Cases
      >- (rename1 ‘Ret x’ >> Cases_on ‘x’ >>
          rw[chor_itree_merge_def] >>
          match_mp_tac rooted_can_act >>
          iforest_simp) >>
      rw[chor_itree_merge_def] >>
      match_mp_tac rooted_can_act >>
      iforest_simp)
  >- (Cases
      >- (rename1 ‘Ret x’ >> Cases_on ‘x’ >>
          rw[chor_itree_merge_def]
          >~ [‘FLOOKUP _.forest _ = SOME (Vis _ _)’]
          >- (qpat_x_assum ‘rooted (_ with forest := _.forest |+ (_,Vis _ _)) _’ mp_tac >>
              match_mp_tac(DECIDE “(A = B) ⇒ (A ⇒ B)”) >>
              rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
              rw[iforest_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE] >>
              rw[] >> rw[]) >>
          match_mp_tac rooted_can_act >>
          iforest_simp) >>
      rw[chor_itree_merge_def]
      >~ [‘FLOOKUP _.forest _ = SOME (Vis _ _)’]
      >- (drule rooted_Vis_switch_cont >>
          simp[FLOOKUP_UPDATE] >>
          rename1 ‘FLOOKUP f.forest p = SOME (Vis a cont)’ >> (* destructive rename*)
          disch_then (qspec_then ‘cont’ mp_tac) >>
          match_mp_tac(DECIDE “(A = B) ⇒ (A ⇒ B)”) >>
          rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
          rw[iforest_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE] >>
          rw[] >> rw[]) >>
      match_mp_tac rooted_can_act >>
      iforest_simp)
QED

Theorem chor_itree_merge_Ret_End:
  chor_itree_merge it (Ret End) =
  if it = Ret End ∨ it = Ret Done then Ret End
  else Ret Unproj
Proof
  Cases_on ‘it’ >> rw[] >> rw[chor_itree_merge_def] >>
  rename1 ‘Ret x’ >> Cases_on ‘x’ >>
  gvs[chor_itree_merge_def]
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
          \\ iforest_simp
          >- (gvs[no_self_comunication_def]
              \\ imp_res_tac (cj 3 no_undefined_vars_simps)
              \\ last_x_assum $ drule_all_then assume_tac
              \\ reverse $ Cases_on ‘MEM p (procsOf c')’
              >- (gvs[MEM_procsOf_chor_itree]
                  \\ rw[chor_itree_merge_Ret_End]
                  \\ match_mp_tac rooted_can_act
                  \\ simp[iforest_can_act_def,iforest_get_def,FLOOKUP_UPDATE])
              \\ last_x_assum $ drule_all_then assume_tac
              \\ rw[Once rooted_cases]
              \\ rw[DISJ_EQ_IMP]
              \\ qexists_tac ‘s’
              \\ iforest_simp
              \\ cheat
              )
          >- cheat
          >- gvs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP,lookup_projectS'])
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

Definition iforest_chor_upd_act_def:
  iforest_chor_upd_act ψ = (ψ.act = chor_iforest_act ∧ ψ.upd = chor_iforest_upd)
End

Theorem iforest_chor_upd_act_iforest_cong:
  ∀ψ. iforest_chor_upd_act ψ ⇒ iforest_cong ψ
Proof
  rw[iforest_chor_upd_act_def,iforest_cong_def,non_interference_def]
  \\ gvs[IS_SOME_EXISTS]
  \\ Cases_on ‘e1’ \\ Cases_on ‘e2’
  \\ gvs[FLOOKUP_UPDATE,CaseEq"option",CaseEq"list",DOMSUB_FLOOKUP_NEQ,FUPDATE_COMMUTES]
  \\ TRY (IF_CASES_TAC \\ gs[libTheory.the_def] \\ NO_TAC)
  \\ TRY (CASE_TAC \\ gs[]
          \\ CASE_TAC \\ gs[DOMSUB_FLOOKUP_NEQ]
          \\ CASE_TAC \\ gs[DOMSUB_FLOOKUP_NEQ,FLOOKUP_UPDATE] \\ NO_TAC)
QED

Theorem iforest_cong_can_act_step:
  ∀ψ p q.
    iforest_cong ψ ∧
    p ≠ q ∧
    iforest_can_act ψ p ⇒
    iforest_can_act (iforest_step ψ q) p
Proof
  rw[iforest_cong_def,non_interference_def]
  \\ iforest_simp \\ EVERY_CASE_TAC
  \\ gvs[DOMSUB_FLOOKUP_NEQ,FLOOKUP_UPDATE]
  \\ metis_tac []
QED

Theorem iforest_chor_act_swap:
  ∀ψ p q.
    iforest_chor_upd_act ψ ∧
    p ≠ q ∧
    iforest_can_act ψ p ∧
    iforest_can_act ψ q ⇒
    (iforest_step (iforest_step ψ q) p) = (iforest_step (iforest_step ψ p) q)
Proof
  iforest_simp \\ EVERY_CASE_TAC
  \\ gvs [iforest_component_equality,DOMSUB_FLOOKUP,DOMSUB_FLOOKUP_NEQ,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
  \\ TRY (rw [fmap_eq_flookup,DOMSUB_FLOOKUP,DOMSUB_FLOOKUP_NEQ,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
          \\ IF_CASES_TAC \\ rw[] \\ NO_TAC)
  \\ gs[iforest_chor_upd_act_def]
  >- (Cases_on ‘a’ \\ Cases_on ‘a'’
      \\ gvs[FLOOKUP_UPDATE,CaseEq"option",CaseEq"list",DOMSUB_FLOOKUP_NEQ]
      \\ Cases_on ‘xs’ \\ gvs[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_NEQ])
  >- (Cases_on ‘a’ \\ Cases_on ‘a'’
      \\ gvs[FLOOKUP_UPDATE,CaseEq"option",CaseEq"list",DOMSUB_FLOOKUP_NEQ]
      \\ TRY (Cases_on ‘s = p ∧ q = s'’ \\ gvs[] \\ NO_TAC)
      \\ Cases_on ‘xs’ \\ gvs[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_NEQ])
  >- (Cases_on ‘a’ \\ Cases_on ‘a'’
      \\ gvs[FLOOKUP_UPDATE,CaseEq"option",CaseEq"list",DOMSUB_FLOOKUP_NEQ]
      \\ TRY (Cases_on ‘s' = q ∧ p = s’ \\ gvs[] \\ NO_TAC)
      \\ Cases_on ‘xs''’ \\ gvs[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_NEQ])
  >- (Cases_on ‘a’ \\ Cases_on ‘a'’
      \\ gvs[FLOOKUP_UPDATE,CaseEq"option",CaseEq"list",DOMSUB_FLOOKUP_NEQ,FUPDATE_COMMUTES]
      >- (Cases_on ‘s = p ∧ q = s'’ \\ gvs[libTheory.the_def]
          >-(Cases_on ‘xs'’ \\ gvs[libTheory.the_def,FLOOKUP_UPDATE])
          >- (Cases_on ‘xs’
              \\ gvs[libTheory.the_def,FLOOKUP_UPDATE,DOMSUB_FUPDATE_NEQ,DOMSUB_FLOOKUP_NEQ,FUPDATE_COMMUTES]
              \\ metis_tac []))
      \\ TRY (Cases_on ‘s = p ∧ q = s'’ \\ gvs[libTheory.the_def]
              >-(Cases_on ‘xs'’ \\ gvs[libTheory.the_def,FLOOKUP_UPDATE])
              >- (Cases_on ‘xs’
                  \\ gvs[libTheory.the_def,FLOOKUP_UPDATE,DOMSUB_FUPDATE_NEQ
                        ,DOMSUB_FLOOKUP_NEQ,FUPDATE_COMMUTES]
                  \\ metis_tac [])
              \\ NO_TAC)
      \\ TRY (Cases_on ‘s' = q ∧ p = s’ \\ gvs[libTheory.the_def]
              >-(Cases_on ‘xs’ \\ gvs[libTheory.the_def,FLOOKUP_UPDATE])
              >- (Cases_on ‘xs’
                  \\ gvs[libTheory.the_def,FLOOKUP_UPDATE
                         ,DOMSUB_FUPDATE_NEQ,DOMSUB_FLOOKUP_NEQ,FUPDATE_COMMUTES]
                  \\ metis_tac [])
              \\ NO_TAC)
      \\ TRY (Cases_on ‘xs’ \\ gvs[DOMSUB_FLOOKUP_NEQ,FLOOKUP_UPDATE]
              \\ Cases_on ‘xs'’ \\  gvs[DOMSUB_FLOOKUP_NEQ,FLOOKUP_UPDATE]
              \\ rw [fmap_eq_flookup,DOMSUB_FLOOKUP,DOMSUB_FLOOKUP_NEQ,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
              \\ IF_CASES_TAC \\ rw[]
              \\ NO_TAC))
QED

Definition iforest_steps_def:
  iforest_steps [] ψ      = SOME ψ
  ∧ iforest_steps (p::xs) ψ = if iforest_can_act ψ p
                              then iforest_steps xs (iforest_step ψ p)
                              else NONE
End

Theorem iforest_chor_upd_act_step_idem:
  ∀ψ p. iforest_chor_upd_act ψ ⇔ iforest_chor_upd_act (iforest_step ψ p)
Proof
  iforest_tac [iforest_chor_upd_act_def] \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem iforest_steps_chor_swap:
  ∀l p ψ ψ'.
    iforest_chor_upd_act ψ ∧
    ¬MEM p l ∧
    iforest_can_act ψ p ∧
    iforest_steps l ψ = SOME ψ'
    ⇒
    iforest_steps (p::l) ψ = SOME (iforest_step ψ' p)
Proof
  Induct \\ rw[iforest_steps_def]
  >- (drule iforest_chor_upd_act_iforest_cong \\ strip_tac
      \\ qpat_x_assum ‘_ ≠ _’ (assume_tac o GSYM)
      \\ drule_all iforest_cong_can_act_step
      \\ simp[])
  \\ drule_all_then (mp_tac o GSYM) iforest_chor_act_swap
  \\ rw[]
  \\ qsuff_tac ‘iforest_steps (p::l) (iforest_step ψ h) =
      SOME (iforest_step ψ' p)’
  >- simp[iforest_steps_def]
  \\ metis_tac [ iforest_chor_upd_act_step_idem
               , iforest_cong_can_act_step
               , iforest_chor_upd_act_iforest_cong]
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
  (∀c s.
     to_chor_forest (chor_iforest c s)) ∧
[~step:]
  (∀p ψ.
     iforest_can_act ψ p ∧
     (∀p. iforest_can_act ψ p ⇒ to_chor_forest (iforest_step ψ p)) ⇒
     to_chor_forest ψ)
End

Inductive todo_for_chor:
[~init:]
  (∀c s.
     todo_for_chor [] (chor_iforest c s)) ∧
[~todo:]
  (∀ψ p l.
     todo_for_chor l (iforest_step ψ p) ∧ iforest_can_act ψ p ⇒
           todo_for_chor (p::l) ψ)
End

Definition todo_chor_def:
  todo_chor l ψ =
  ∃c s. iforest_steps l ψ = SOME (chor_iforest c s)
End

Theorem chor_steps_chor:
  iforest_step (chor_iforest c s) p = ψ ⇒
  ∃l c' s'. iforest_steps l ψ = SOME (chor_iforest c' s')
Proof
  cheat
QED

Theorem iforest_steps_APPEND:
  iforest_steps (x++y) ψ = SOME ψ' ⇔
    ∃ψ''. iforest_steps x ψ = SOME ψ'' ∧ iforest_steps y ψ'' = SOME ψ'
Proof
  qid_spec_tac ‘ψ’
  \\ Induct_on ‘x’ \\ fs [iforest_steps_def]
  \\ rw [] \\ eq_tac \\ rw []
  \\ res_tac \\ fs []
QED

Theorem todo_chor_iforest_step:
  iforest_chor_upd_act ψ ∧
  todo_chor l ψ ∧
  iforest_can_act ψ p
  ⇒ ∃l'. todo_chor l' (iforest_step ψ p)
Proof
  rw[todo_chor_def]
  \\ qsuff_tac ‘∃l' c s. iforest_steps (p::l') ψ = SOME (chor_iforest c s)’
  >- fs[iforest_steps_def]
  \\ reverse (Cases_on ‘MEM p l’)
  >- (drule_all iforest_steps_chor_swap \\ rw[]
      \\ ‘∃y. iforest_step (chor_iforest c s) p = y’ by simp[]
      \\ drule chor_steps_chor
      \\ fs[] \\ strip_tac
      \\ qexists_tac ‘l ++ l'’
      \\ metis_tac [GSYM APPEND,iforest_steps_APPEND])
  >- (pop_assum (mp_tac o ONCE_REWRITE_RULE [MEM_SPLIT_APPEND_first])
      \\ rw[]
      \\ qexists_tac ‘pfx++sfx’
      \\ qexistsl_tac [‘c’,‘s’]
      \\ ONCE_REWRITE_TAC [GSYM APPEND]
      \\ REWRITE_TAC [iforest_steps_APPEND]
      \\ gs[iforest_steps_APPEND]
      \\ drule_all iforest_steps_chor_swap
      \\ strip_tac \\ fs[]
      \\ gvs[iforest_steps_def])
QED

(*
Theorem iforest_step_to_chor_forest:
  ∀c s p.
    MEM p (procsOf c) ⇒
    to_chor_forest (iforest_step (chor_iforest c s) p)
Proof
  Induct \\ rw[]
  >- iforest_simp
  >- cheat (* If *)
  >- (gs[procsOf_def,nub'_def,nub'_APPEND,nub'_procsOf,dvarsOf_def] \\ cheat)
  \\ cheat
QED
*)

Theorem iforest_step_skip:
  ¬iforest_can_act ψ p ⇒ iforest_step ψ p = ψ
Proof
  fs [iforest_can_act_def,iforest_step_def,AllCaseEqs()]
  \\ Cases_on ‘iforest_get ψ p’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ fs [iforest_upd_def]
QED

(*
Theorem iforest_step_preserves_to_chor_forest:
  ∀ψ. to_chor_forest ψ ⇒ to_chor_forest (iforest_step ψ p)
Proof
  rw[]
  \\ first_assum mp_tac
  \\ simp_tac std_ss [Once to_chor_forest_cases] \\ reverse (rw[])
  >- (Cases_on ‘iforest_can_act ψ p’
      \\ metis_tac [iforest_step_skip])
  >- (Cases_on ‘p ∈ iforest_itrees (chor_iforest c s)’
      >- fs[iforest_step_to_chor_forest,chor_iforest_itrees_eq_procOf]
      >- (iforest_simp \\ simp[FLOOKUP_DEF]))
QED

Theorem iforest_steps_IMP_Res:
  ∀f res.
    iforest_steps f res ⇒
    ∀c p.
      to_chor_forest f ∧ p ∈ iforest_itrees f ⇒
      EXISTS (λ(q,a). p = q ∧ ∃t. a = Res t) res
Proof
  Induct_on ‘iforest_steps’ \\ rpt strip_tac
  >- (gvs [SUBSET_DEF]
      \\ fs [Once to_chor_forest_cases] \\ gvs []
      \\ gvs [chor_iforest_itrees_eq_procOf]
      \\ metis_tac [iforest_can_act_exists])
  \\ gvs []
  \\ rewrite_tac [METIS_PROVE [] “b ∨ c ⇔ ~b ⇒ c”]
  \\ strip_tac
  \\ first_x_assum irule
  \\ irule_at Any iforest_step_preserves_to_chor_forest
  \\ fs []
  \\ pairarg_tac \\ fs []
  \\ iforest_simp \\ fs [FLOOKUP_DEF]
  \\ Cases_on ‘p' = q’ \\ gvs []
  \\ every_case_tac \\ gvs [iforest_get_def,FLOOKUP_DEF]
  \\ CCONTR_TAC \\ gvs []
  \\ gvs [iforest_act_def,iforest_get_def,FLOOKUP_DEF]
QED

Theorem chor_iforest_deadlock_freedom:
  ∀procs c s.
    fair_trace (set (procsOf c)) procs
    ⇒ deadlock_freedom (set (procsOf c)) (iforest (chor_iforest c s) procs)
Proof
  simp [deadlock_freedom_def]
  \\ rpt gen_tac \\ strip_tac
  \\ conj_asm1_tac
  >- simp [iforestTheory.actions_end_iforest]
  \\ CCONTR_TAC \\ fs []
  \\ ‘fair_trace (iforest_itrees (chor_iforest c s)) procs’ by
        fs [chor_iforest_itrees_eq_procOf]
  \\ drule_all LFINITE_iforest
  \\ strip_tac \\ fs [exists_fromList]
  \\ drule iforest_steps_IMP_Res \\ simp []
  \\ irule_at Any to_chor_forest_init
  \\ first_x_assum $ irule_at Any \\ fs []
  \\ fs [chor_iforest_itrees_eq_procOf]
QED
*)

Inductive iforest_run:
  (∀ψ.
    (∀p. ¬iforest_can_act ψ p) ⇒
    iforest_run ψ ψ) ∧
  (∀ψ p res.
    iforest_can_act ψ p ∧
    iforest_run (iforest_step ψ p) res ⇒
    iforest_run ψ res)
End

Definition finally_empty_def:
  finally_empty ψ ⇔
    (* every terminating run results in an empty forest *)
    ∀ψ'. iforest_run ψ ψ' ⇒ iforest_itrees ψ' = ∅
End

(*
Theorem from_chor_finally_empty:
  from_chor_forest c ψ ⇒ finally_empty ψ
Proof
  rw[finally_empty_def]
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘c’
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘ψ'’,‘ψ’]
  \\ ho_match_mp_tac iforest_run_ind
  \\ rw[]
  >- (last_x_assum mp_tac
      \\ pop_assum mp_tac
      \\ MAP_EVERY qid_spec_tac [‘ψ’,‘c’]
      \\ ho_match_mp_tac from_chor_forest_ind
      \\ rw[]
      >- cheat (* Should be true *)
      >- cheat) (* Not true *)
  >- (first_x_assum irule
      \\ irule_at Any from_chor_forest_step
      \\ metis_tac [])
QED
*)

Theorem iforest_chor_upd_act_chor_iforest:
  iforest_chor_upd_act (chor_iforest c s)
Proof
  iforest_tac [iforest_chor_upd_act_def]
QED

Theorem iforest_chor_upd_act_iforest_step:
  iforest_chor_upd_act s ⇒
  iforest_chor_upd_act (iforest_step s p)
Proof
  simp[iforest_chor_upd_act_step_idem]
QED

Theorem ifrest_run_inv:
  ∀s t.
    iforest_run s t ⇒
    ∀l. iforest_chor_upd_act s ∧
        todo_chor l s ⇒
        iforest_itrees t = ∅
Proof
  Induct_on ‘iforest_run’ \\ rw []
  >-
   (Cases_on ‘l’ \\ gvs [todo_chor_def,iforest_steps_def]
    \\ fs [chor_iforest_itrees_eq_procOf]
    \\ CCONTR_TAC
    \\ ‘∃x. MEM x (procsOf c)’ by (Cases_on ‘procsOf c’ \\ fs [] \\ metis_tac [])
    \\ drule iforest_can_act_exists
    \\ metis_tac [])
  \\ first_x_assum irule
  \\ fs [iforest_chor_upd_act_iforest_step]
  \\ irule todo_chor_iforest_step \\ fs []
  \\ first_x_assum $ irule_at Any
QED

Theorem finally_empty_chor_iforest:
  finally_empty (chor_iforest c s)
Proof
  rw [finally_empty_def]
  \\ drule ifrest_run_inv
  \\ disch_then $ qspec_then ‘[]’ irule
  \\ fs [todo_chor_def,iforest_steps_def,iforest_chor_upd_act_chor_iforest]
  \\ irule_at Any EQ_REFL
QED

Inductive iforest_steps:
  (∀ψ.
    (∀p. ¬iforest_can_act ψ p) ⇒
    iforest_steps ψ []) ∧
  (∀ψ p res.
    iforest_can_act ψ p ∧
    iforest_steps (iforest_step ψ p) res ⇒
    iforest_steps ψ (iforest_act ψ p::res))
End

Theorem LFINITE_iforest:
  LFINITE (iforest f trace) ∧ fair_trace (iforest_itrees f) trace ⇒
  ∃res.
    iforest f trace = fromList res ∧
    iforest_steps f res
Proof
  strip_tac
  \\ dxrule LFINITE_IMP_fromList
  \\ strip_tac \\ fs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
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
    \\ imp_res_tac iforest_can_act_in_itrees
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
  \\ last_x_assum $ irule_at Any
  \\ drule iforestTheory.LDROP_WHILE_EQ_CONS
  \\ strip_tac \\ gvs []
  \\ irule fair_trace_procs_subset
  \\ irule_at Any iforest_itrees_mono_step \\ fs []
  \\ imp_res_tac iforest_can_act_in_itrees \\ fs []
QED

Theorem finally_empty_thm:
  ∀f res.
    iforest_steps f res ⇒
    ∀c p.
      finally_empty f ∧ p ∈ iforest_itrees f ⇒
      EXISTS (λ(q,a). p = q ∧ ∃t. a = Res t) res
Proof
  Induct_on ‘iforest_steps’ \\ rpt strip_tac
  >- (fs [finally_empty_def]
      \\ first_x_assum $ qspec_then ‘f’ mp_tac
      \\ impl_tac >- simp [Once iforest_run_cases]
      \\ fs [EXTENSION] \\ pop_assum $ irule_at Any)
  \\ gvs []
  \\ rewrite_tac [METIS_PROVE [] “b ∨ c ⇔ ~b ⇒ c”]
  \\ strip_tac
  \\ first_x_assum irule
  \\ conj_tac
  >-
   (fs [finally_empty_def] \\ rw []
    \\ first_x_assum irule
    \\ simp [Once iforest_run_cases]
    \\ metis_tac [])
  \\ pairarg_tac \\ fs []
  \\ iforest_simp \\ fs [FLOOKUP_DEF]
  \\ Cases_on ‘p' = q’ \\ gvs []
  \\ every_case_tac \\ gvs [iforest_get_def,FLOOKUP_DEF]
  \\ CCONTR_TAC \\ gvs []
  \\ gvs [iforest_act_def,iforest_get_def,FLOOKUP_DEF]
QED

Theorem chor_iforest_deadlock_freedom:
  ∀procs c s.
    fair_trace (set (procsOf c)) procs
    ⇒ deadlock_freedom (set (procsOf c)) (iforest (chor_iforest c s) procs)
Proof
  simp [deadlock_freedom_def]
  \\ rpt gen_tac \\ strip_tac
  \\ conj_asm1_tac
  >- simp [iforestTheory.actions_end_iforest]
  \\ CCONTR_TAC \\ fs []
  \\ ‘fair_trace (iforest_itrees (chor_iforest c s)) procs’ by
        fs [chor_iforest_itrees_eq_procOf]
  \\ drule_all LFINITE_iforest
  \\ strip_tac \\ fs [exists_fromList]
  \\ drule finally_empty_thm \\ simp []
  \\ first_x_assum $ irule_at Any \\ fs []
  \\ fs [chor_iforest_itrees_eq_procOf,finally_empty_chor_iforest]
QED

(*
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
*)

val _ = export_theory ()
