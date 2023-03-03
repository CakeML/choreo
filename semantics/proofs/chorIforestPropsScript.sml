open preamble choreoUtilsTheory chorLangTheory chorLangPropsTheory
     itreeTauTheory iforestTheory itreeCommonTheory itreePropsTheory
     chorItreeSemTheory chorIforestSemTheory chor_to_endpointPropsTheory

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

Theorem chor_forest_split:
  ∀l c p st.
    MEM p l ⇒
    chor_forest c st l =
    chor_forest c st (FILTER (λy. y ≠ p) l) |+ (p,chor_itree p (projectS p st) c)
Proof
  rw [] \\ Induct_on ‘l’ \\ rw[chor_forest_def] \\ rw[FUPDATE_EQ]
  >- metis_tac [FUPDATE_COMMUTES]
  >- (Cases_on ‘MEM h l’
      >- (first_x_assum drule \\ rw[])
      >- (AP_THM_TAC
          \\ AP_TERM_TAC
          \\ AP_TERM_TAC
          \\ Induct_on ‘l’ \\ rw[]))
QED

Theorem FLOOKUP_chor_forest:
  ∀c s ps p.
    FLOOKUP (chor_forest c s ps) p =
    if MEM p ps then
      SOME(chor_itree p (projectS p s) c)
    else
      NONE
Proof
  Induct_on ‘ps’ \\
  rw[chor_forest_def,FLOOKUP_UPDATE] \\
  gvs[]
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

Theorem chor_forest_sel_idem:
  ∀c s p q b l.
  ¬ MEM p l ∧ ¬ MEM q l
  ⇒ chor_forest (Sel p b q c) s l = chor_forest c s l
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

Definition iforest_steps_no_error_def:
  iforest_steps_no_error [] ψ      = SOME ψ
  ∧ iforest_steps_no_error (p::xs) ψ = if iforest_can_act ψ p ∧ iforest_get ψ p ≠ SOME(Ret Error)
                              then
                                iforest_steps_no_error xs (iforest_step ψ p)
                              else NONE
End

Theorem iforest_chor_upd_act_step_idem:
  ∀ψ p. iforest_chor_upd_act ψ ⇔ iforest_chor_upd_act (iforest_step ψ p)
Proof
  iforest_tac [iforest_chor_upd_act_def] \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem iforest_chor_upd_act_chor_iforest:
  iforest_chor_upd_act (chor_iforest c s)
Proof
  iforest_tac [iforest_chor_upd_act_def]
QED

Theorem iforest_chor_upd_act_iforest_step:
  iforest_chor_upd_act s ⇒
  iforest_chor_upd_act (iforest_step s p)
Proof
  simp[GSYM iforest_chor_upd_act_step_idem]
QED

Theorem iforest_step_skip:
  ¬iforest_can_act ψ p ⇒ iforest_step ψ p = ψ
Proof
  fs [iforest_can_act_def,iforest_step_def,AllCaseEqs()]
  \\ Cases_on ‘iforest_get ψ p’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ fs [iforest_upd_def]
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

Theorem iforest_get_iforest_step:
  h ≠ p ⇒ iforest_get(iforest_step ψ h) p = iforest_get ψ p
Proof
  iforest_simp >>
  every_case_tac >> gvs[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM]
QED

Theorem iforest_steps_no_error_APPEND:
  ∀ps qs ψ ψ'.
    iforest_steps_no_error (ps ++ qs) ψ =
    case iforest_steps_no_error ps ψ of
      NONE => NONE
    | SOME ψ' => iforest_steps_no_error qs ψ'
Proof
  Induct >> rw[iforest_steps_no_error_def]
QED

Theorem iforest_chor_upd_act_steps_no_error_pres:
  ∀ψ l ψ'.
    iforest_chor_upd_act ψ ∧ iforest_steps_no_error l ψ = SOME ψ' ⇒
    iforest_chor_upd_act ψ'
Proof
  Induct_on ‘l’ >> rw[iforest_steps_no_error_def,AllCaseEqs()] >>
  simp[] >> metis_tac[iforest_chor_upd_act_step_idem]
QED

Theorem iforest_steps_no_error_chor_swap:
  ∀l p ψ ψ'.
    iforest_chor_upd_act ψ ∧
    ¬MEM p l ∧
    iforest_can_act ψ p ∧
    iforest_get ψ p ≠ SOME(Ret Error) ∧
    iforest_steps_no_error l ψ = SOME ψ'
    ⇒
    iforest_steps_no_error (p::l) ψ = SOME (iforest_step ψ' p)
Proof
  Induct \\ rw[iforest_steps_no_error_def]
  >- (drule iforest_chor_upd_act_iforest_cong \\ strip_tac
      \\ qpat_x_assum ‘_ ≠ _’ (assume_tac o GSYM)
      \\ metis_tac[iforest_cong_can_act_step])
  \\ drule_all_then (mp_tac o GSYM) iforest_chor_act_swap
  \\ rw[]
  >- (last_x_assum kall_tac \\ iforest_simp \\ every_case_tac \\ gvs[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM])
  \\ ‘iforest_get (iforest_step ψ h) p ≠ SOME (Ret Error)’
    by(rw[iforest_get_iforest_step])
  \\ qsuff_tac ‘iforest_steps_no_error (p::l) (iforest_step ψ h) =
      SOME (iforest_step ψ' p)’
  >- simp[iforest_steps_no_error_def]
  \\ metis_tac [ iforest_chor_upd_act_step_idem
               , iforest_cong_can_act_step
               , iforest_chor_upd_act_iforest_cong]
QED

Definition up_forest_def:
  up_forest ψ = ψ with forest := FMAP_MAP2 (↑ o SND) ψ.forest
End

Overload "↑" = “up_forest”;

Definition todo_chor_def:
  todo_chor l ψ =
  ∃c s. iforest_steps l ψ = SOME (↑ (chor_iforest c s)) ∧
        dvarsOf c = [] ∧ no_undefined_vars (s,c) ∧
        no_self_comunication c ∧
        compile_network_ok s c (procsOf c)
End

Theorem MEM_iforest_step_idem:
  ¬MEM p (procsOf c) ⇒ iforest_step (chor_iforest c s) p = chor_iforest c s
Proof
  rw[iforest_step_def,iforest_get_def,chor_iforest_def]
  \\ qmatch_asmsub_rename_tac ‘MEM p ll’
  \\ ‘FLOOKUP (chor_forest c s ll) p = NONE’ suffices_by simp[]
  \\ Induct_on ‘ll’ \\ rw[chor_forest_def,FLOOKUP_UPDATE]
QED

Theorem iforest_can_act_MEM:
  iforest_can_act (chor_iforest c s) p ⇒ MEM p (procsOf c)
Proof
  rw[iforest_can_act_def] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  gvs[iforest_get_def,chor_iforest_def,FLOOKUP_chor_forest]
QED

(*yuck*)
Theorem iforest_can_act_MEM':
  iforest_can_act (iforest_step(chor_iforest c s) q) p ⇒ MEM p (procsOf c)
Proof
  rw[iforest_can_act_def,iforest_step_def,iforest_get_def] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  gvs[iforest_get_def,chor_iforest_def,FLOOKUP_chor_forest,iforest_del_def,DOMSUB_FLOOKUP_THM,iforest_set_def,FLOOKUP_UPDATE,AllCaseEqs(),iforest_upd_def,IS_SOME_EXISTS] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  gvs[FLOOKUP_chor_forest,AllCaseEqs(),FLOOKUP_UPDATE]
QED

Theorem iforest_step_par_pres:
  q ∉ (FDOM (i.forest)) ∧ p ≠ q
  ⇒
  iforest_step (i with forest := i.forest |+ (q,t)) p = (iforest_step i p) with forest := (iforest_step i p).forest |+ (q,t)
Proof
  rw[iforest_step_def,iforest_get_def,FLOOKUP_UPDATE] \\
  Cases_on ‘FLOOKUP i.forest p’ \\
  gvs[] \\
  rename1 ‘itree_CASE x’ \\ Cases_on ‘x’ \\
  gvs[iforest_del_def,iforest_set_def,iforest_upd_def]
  THEN1 (rw[iforest_component_equality,fmap_eq_flookup] \\
         gvs[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM] \\
         rw[])
  THEN1 (rw[iforest_component_equality,fmap_eq_flookup] \\
         gvs[FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM] \\
         rw[]) \\
  TOP_CASE_TAC \\ rw[iforest_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM] \\ rw[]
QED

Theorem iforest_steps_par_pres:
  ∀ps i i' q t.
  q ∉ (FDOM (i.forest)) ∧ ¬MEM q ps ∧ (iforest_steps ps i = SOME i')
  ⇒
  (iforest_steps ps (i with forest := i.forest |+ (q,t)) = SOME(i' with forest := i'.forest |+ (q,t)))
Proof
  Induct \\ rw[iforest_steps_def]
  THEN1 gvs[iforest_can_act_def,iforest_get_def,FLOOKUP_UPDATE] \\
  simp[iforest_step_par_pres] \\
  first_x_assum $ drule_at $ Pos last \\
  disch_then $ drule_at $ Pos last \\
  disch_then (qspec_then ‘t’ mp_tac) \\
  iforest_simp \\ every_case_tac \\ gvs[]
QED

Theorem iforest_step_FDOM_mono:
  q ∈ FDOM (iforest_step i p).forest ⇒ q ∈ FDOM(i.forest)
Proof
  rw[iforest_step_def,iforest_get_def] \\
  rpt(PURE_FULL_CASE_TAC \\ gvs[iforest_upd_def,iforest_set_def,iforest_del_def]) \\
  gvs[FDOM_FLOOKUP]
QED

Theorem iforest_steps_FDOM_mono:
  ∀ps i i' q.
    iforest_steps ps i = SOME i' ∧ q ∈ FDOM i'.forest ⇒ q ∈ FDOM(i.forest)
Proof
  Induct \\
  rw[iforest_steps_def] \\
  metis_tac[iforest_step_FDOM_mono]
QED

Theorem iforest_steps_fresh_steps:
  ∀ps i i' q.
    iforest_steps ps i = SOME i' ∧ q ∉ FDOM i.forest ⇒ ¬MEM q ps
Proof
  Induct \\
  rw[iforest_steps_def] \\
  gvs[iforest_can_act_def,iforest_get_def]
  THEN1 (CCONTR_TAC \\ gvs[GSYM flookup_thm]) \\
  first_x_assum $ drule_then match_mp_tac \\
  metis_tac[iforest_step_FDOM_mono]
QED

Theorem free_variables_procsOf:
  ∀c x p. (x,p) ∈ free_variables c ⇒ MEM p (procsOf c)
Proof
  Induct \\ rw[procsOf_def,free_variables_def, MEM_nub',MEM_MAP] \\
  metis_tac[]
QED

Theorem iforest_can_act_step_idem:
  ¬iforest_can_act i p ⇒ iforest_step i p = i
Proof
  iforest_simp \\ every_case_tac \\ gvs[]
QED

Theorem chor_forest_perm:
  ∀l l'. PERM l l' ∧ ALL_DISTINCT l ⇒ chor_forest c s l = chor_forest c s l'
Proof
  Induct_on ‘PERM’ \\
  rw[chor_forest_def] \\
  rw[fmap_eq_flookup,FLOOKUP_UPDATE] \\ rw[] \\
  metis_tac[ALL_DISTINCT_PERM]
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

Theorem chor_itree_merge_Error:
  ∀t1 t2.
    chor_itree_merge t1 t2 = Ret Error ⇔ (t1 = Ret Error ∧ t2 = Ret Error) ∨
                                         (t1 = Ret Done ∧ t2 = Ret Error) ∨
                                         (t1 = Ret Error ∧ t2 = Ret Done)
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’ \\
  rw[chor_itree_merge_def] \\
  TRY $ Cases_on ‘x’ \\ TRY $ Cases_on ‘x'’ \\
  gvs[chor_itree_merge_def]
QED

Theorem project_ok_ifL:
  project_ok q dvars (IfThen v p c1 c2) ⇒ project_ok q dvars c1
Proof
  rw[project_def] \\
  every_case_tac \\
  gvs[] \\
  metis_tac[split_sel_project_ok]
QED

Theorem project_ok_ifR:
  project_ok q dvars (IfThen v p c1 c2) ⇒ project_ok q dvars c2
Proof
  rw[project_def] \\
  every_case_tac \\
  gvs[] \\
  metis_tac[split_sel_project_ok]
QED

Theorem no_undefined_vars_Let:
  no_undefined_vars (s,Let p v f l c) ⇒
  no_undefined_vars (s |+ ((p,v),x),c)
Proof
  rw[no_undefined_vars_def,free_variables_def,SUBSET_DEF,MEM_MAP, PULL_EXISTS, SF DNF_ss] \\
  metis_tac[]
QED

Theorem chor_itree_not_error:
  dvarsOf c = [] ∧
  no_undefined_vars (s,c) ∧
  no_self_comunication c ∧
  chor_itree p (projectS p s) c = Ret Error ⇒ F
Proof
  MAP_EVERY qid_spec_tac $ rev [‘t’,‘c’,‘s’] \\
  Induct_on ‘c’ \\
  rw[] \\
  spose_not_then strip_assume_tac \\
  gvs[no_self_comunication_def,chor_itree_def,AllCaseEqs(),chor_itree_merge_Error] \\
  imp_res_tac no_undefined_vars_simps \\
  imp_res_tac no_undefined_vars_Let \\
  imp_res_tac project_ok_ifL \\
  imp_res_tac project_ok_ifR \\
  gvs[dvarsOf_def,nub'_dvarsOf,nub'_nil] \\
  imp_res_tac no_undefined_vars_def \\
  gvs[free_variables_def,SUBSET_DEF,FDOM_FLOOKUP,SF DNF_ss,lookup_projectS',
      MEM_MAP,EXISTS_MEM] \\
  gvs[project_def] \\
  metis_tac[fupdate_projectS,NOT_SOME_NONE]
QED

Theorem iforest_steps_middle_swap:
  ∀l1 l2 p ψ ψ1 ψ2.
  ¬ MEM p l1
  ∧ iforest_chor_upd_act ψ
  ∧ iforest_can_act ψ p
  ∧ iforest_steps l1 ψ = SOME ψ1
  ∧ iforest_steps l2 (iforest_step ψ1 p) = SOME ψ2
  ⇒ iforest_steps (l1++l2) (iforest_step ψ p) = SOME ψ2
Proof
  Induct \\ rw[]
  >- gs[iforest_steps_def]
  \\ simp[iforest_steps_def]
  \\ conj_asm1_tac
  >- (irule iforest_cong_can_act_step
      \\ gs[iforest_steps_def,iforest_chor_upd_act_iforest_cong])
  \\ dep_rewrite.DEP_ONCE_REWRITE_TAC[iforest_chor_act_swap]
  \\ conj_tac >- gvs[iforest_steps_def]
  \\ first_x_assum irule
  \\ first_x_assum (irule_at Any)
  \\ gvs[iforest_chor_upd_act_iforest_step,iforest_steps_def]
  \\ irule iforest_cong_can_act_step
  \\ gs[iforest_steps_def,iforest_chor_upd_act_iforest_cong]
QED

Theorem iforest_step_no_error:
  ∀ψ p l ψ' p'.
    iforest_steps_no_error l ψ = SOME ψ' ∧ iforest_get ψ' p' ≠ SOME(Ret Error) ⇒
    iforest_get ψ p' ≠ SOME(Ret Error)
Proof
  rw[] >>
  spose_not_then strip_assume_tac >>
  rename1 ‘iforest_steps_no_error _ ψ''’ >>
  rpt $ pop_assum mp_tac >>
  qid_spec_tac ‘ψ''’ >>
  Induct_on ‘l’ >>
  rpt strip_tac >>
  gvs[iforest_steps_no_error_def] >>
  last_x_assum drule >>
  strip_tac >>
  gvs[iforest_step_def] >>
  (* yuck *)
  every_case_tac >>
  gvs[iforest_del_def,iforest_set_def,iforest_upd_def,iforest_get_def,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE] >>
  every_case_tac >> gvs[FLOOKUP_UPDATE] >>
  every_case_tac >> gvs[FLOOKUP_UPDATE]
QED

CoInductive ae_error_free:
  iforest_get ψ p ≠ SOME(Ret Error) ∧
  (∀p'. ∃l ψ'. iforest_steps_no_error l (iforest_step ψ p') = SOME ψ' ∧ ae_error_free p ψ')
  ⇒ ae_error_free p ψ
End

Theorem iforest_can_act_iforest_steps:
  ∀ψ' p l ψ.
  iforest_cong ψ ∧
  ¬MEM p l ∧
  iforest_can_act ψ p ∧
  iforest_steps l ψ = SOME ψ' ⇒ iforest_can_act ψ' p
Proof
  ntac 2 strip_tac >>
  Induct >>
  rw[iforest_steps_def] >> simp[] >>
  last_x_assum match_mp_tac >>
  first_x_assum $ irule_at $ Pos last >>
  simp[iforest_cong_step,iforest_cong_can_act_step]
QED

Theorem iforest_can_act_iforest_steps_no_error:
  ∀ψ' p l ψ.
  iforest_cong ψ ∧
  ¬MEM p l ∧
  iforest_can_act ψ p ∧
  iforest_steps_no_error l ψ = SOME ψ' ⇒ iforest_can_act ψ' p
Proof
  ntac 2 strip_tac >>
  Induct >>
  rw[iforest_steps_no_error_def] >> simp[] >>
  last_x_assum match_mp_tac >>
  first_x_assum $ irule_at $ Pos last >>
  simp[iforest_cong_step,iforest_cong_can_act_step]
QED

Theorem iforest_steps_no_error_innocuous_step:
  ∀l ψ p.
    ¬MEM p l ∧
    iforest_chor_upd_act ψ ∧
    iforest_can_act ψ p ∧
    iforest_steps_no_error l ψ = SOME ψ' ⇒
    iforest_steps_no_error l (iforest_step ψ p) = SOME (iforest_step ψ' p)
Proof
  Induct >> rw[iforest_steps_no_error_def]
  >- (last_x_assum kall_tac >> simp[iforest_cong_can_act_step,iforest_chor_upd_act_iforest_cong])
  >- (last_x_assum kall_tac >> iforest_simp >> every_case_tac >> gvs[DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]) >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[iforest_chor_act_swap] >>
  simp[] >>
  last_x_assum match_mp_tac >>
  simp[GSYM iforest_chor_upd_act_step_idem,iforest_cong_can_act_step,iforest_chor_upd_act_iforest_cong]
QED

Theorem iforest_compose_steps:
  ∀l' l ψ ψ'' ψ'.
    iforest_chor_upd_act ψ ∧
    iforest_steps l' ψ = SOME ψ'' ∧
    iforest_steps_no_error l ψ = SOME ψ' ⇒
    ∃l'' l''' ψ'''. (LENGTH l'' ≤ LENGTH l' ∧ iforest_steps l'' ψ' = SOME ψ''' ∧
                ((iforest_get ψ'' q = SOME(Ret Error)) ⇒ (iforest_get ψ''' q = SOME(Ret Error))))
Proof
  Induct >>
  rw[iforest_steps_def]
  >- metis_tac[iforest_step_no_error] >>
  rename1 ‘iforest_can_act _ p’ >>
  reverse $ Cases_on ‘MEM p l’
  >- (‘iforest_steps_no_error l (iforest_step ψ p) = SOME (iforest_step ψ' p)’
        by(match_mp_tac iforest_steps_no_error_innocuous_step >> simp[]) >>
      first_x_assum $ drule_at $ Pos last >>
      disch_then $ drule_at $ Pos last >>
      impl_tac >- simp[GSYM iforest_chor_upd_act_step_idem] >>
      strip_tac >>
      rename1 ‘LENGTH ml ≤ _’ >>
      qexists_tac ‘p::ml’ >>
      simp[iforest_steps_def] >>
      metis_tac[iforest_can_act_iforest_steps_no_error,iforest_chor_upd_act_iforest_cong]) >>
  gvs[Once MEM_SPLIT_APPEND_first] >>
  rename1 ‘ (ls1 ++ [p] ++ ls2)’ >>
  gvs[iforest_steps_no_error_APPEND,AllCaseEqs(),iforest_steps_no_error_def] >>
  ‘iforest_get ψ p ≠ SOME (Ret Error)’
    by metis_tac[iforest_step_no_error] >>
  drule_all iforest_steps_no_error_chor_swap >>
  rw[iforest_steps_no_error_def] >>
  last_x_assum(qspecl_then [‘ls1 ++ ls2’,‘iforest_step ψ p’] mp_tac) >>
  simp[iforest_steps_no_error_APPEND,AllCaseEqs(),GSYM iforest_chor_upd_act_step_idem] >>
  strip_tac >>
  rename1 ‘LENGTH ml ≤ _’ >>
  qexists_tac ‘ml’ >>
  simp[]
QED

Theorem iforest_steps_no_error:
  ∀l' ψ p' ψ''.
    iforest_chor_upd_act ψ ∧
    iforest_steps l' ψ = SOME ψ'' ∧
    ae_error_free p' ψ ⇒
    iforest_get ψ'' p' ≠ SOME(Ret Error)
Proof
  strip_tac >>
  Induct_on ‘LENGTH l'’ using COMPLETE_INDUCTION >>
  Cases >>
  rw[iforest_steps_def] >> simp[]
  >- gvs[Once ae_error_free_cases] >>
  rename1 ‘iforest_step ψ q’ >>
  qhdtm_x_assum ‘ae_error_free’ $ strip_assume_tac o REWRITE_RULE[Once ae_error_free_cases] >>
  first_x_assum $ qspec_then ‘q’ strip_assume_tac >>
  ‘iforest_chor_upd_act (iforest_step ψ q)’ by simp[GSYM iforest_chor_upd_act_step_idem] >>
  drule_all iforest_compose_steps >>
  disch_then $ qspec_then ‘p'’ strip_assume_tac >>
  rename1 ‘LENGTH ml ≤ LENGTH _’ >>
  last_x_assum(qspec_then ‘LENGTH ml’ mp_tac) >>
  impl_tac >- simp[] >>
  disch_then(qspec_then ‘ml’ mp_tac) >>
  impl_tac >- simp[] >>
  disch_then $ drule_at (Pat ‘_ = _’) >>
  disch_then $ drule_at $ Pos last >>
  impl_tac >- metis_tac[iforest_chor_upd_act_steps_no_error_pres] >>
  simp[] >> metis_tac[]
QED

val forest_chor_tail_tac = (TRY (rw [chor_forest_com_idem,
                                     chor_forest_sel_idem,
                                     chor_forest_st_idem,
                                     MEM_FILTER,FILTER_FILTER,
                                     DOMSUB_NOT_IN_DOM,chor_forest_FDOM]
                                 \\ AP_TERM_TAC
                                 \\ rw[FILTER_EQ]
                                 \\ TRY (qmatch_goalsub_rename_tac ‘FILTER _ ll = ll’
                                         \\ last_x_assum kall_tac
                                         \\ Induct_on ‘ll’
                                         \\ rw[])
                                 \\ metis_tac [])
                            \\ TRY (rw[projectS_fupdate,
                                       no_undefined_FLOOKUP_com,
                                       lookup_projectS,projectS_def]
                                    \\ NO_TAC))

val split_updates_tac = (TRY (qmatch_goalsub_abbrev_tac ‘a1 |+ b1 |+ c1 = a2 |+ b2 |+ c2’
                              \\ ‘a1 = a2 ∧ b1 = b2 ∧ c1 = c2’ suffices_by simp[]
                              \\ UNABBREV_ALL_TAC \\ rw[])
                         \\ TRY (qmatch_goalsub_abbrev_tac ‘a1 |+ b1 = a2 |+ b2 ’
                                 \\ ‘a1 = a2 ∧ b1 = b2’ suffices_by simp[]
                                 \\ UNABBREV_ALL_TAC \\ rw[]))

val iforest_steps_eval = rpt (qmatch_goalsub_abbrev_tac ‘iforest_steps’
                              \\ rw[Once iforest_steps_def]
                              \\rw (iforest_thm @ [FUPDATE_COMMUTES,DOMSUB_FUPDATE_NEQ,DOMSUB_FUPDATE_NEQ]))

Theorem cut_sel_upto_steps:
  ∀p c s.
    no_self_comunication c ∧
    dvarsOf c = [] ⇒
    ∃l. iforest_steps l (chor_iforest c s) = SOME (chor_iforest (cut_sel_upto p c) s)
Proof
  rw[]
  \\ Induct_on ‘c’ \\ rw[cut_sel_upto_def]
  \\ TRY (qexists_tac ‘[]’ \\ rw[iforest_steps_def] \\ NO_TAC)
  \\ Q.REFINE_EXISTS_TAC ‘l1 ++ l2’
  \\ simp[iforest_steps_APPEND]
  \\ gvs[no_self_comunication_def,dvarsOf_def,nub'_dvarsOf]
  \\ first_x_assum (irule_at Any)
  \\ rename1 ‘(Sel q1 b q2 c)’
  \\ Cases_on ‘b’
  \\ (Cases_on ‘MEM q1 (procsOf c)’
      \\ Cases_on ‘MEM q2 (procsOf c)’
      >- (qexists_tac ‘[q1;q2]’
          \\ iforest_steps_eval
          \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split
          \\ ‘MEM q1 (FILTER (λy. y ≠ q2) (procsOf c))’ by simp[MEM_FILTER]
          \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split
          \\ split_updates_tac
          \\ forest_chor_tail_tac)
      >- (qexists_tac ‘[q1;q2;q2]’
          \\ drule_all_then assume_tac MEM_procsOf_chor_itree
          \\ iforest_steps_eval
          \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split
          \\ split_updates_tac
          \\ forest_chor_tail_tac)
      >- (qexists_tac ‘[q1;q2;q1]’
          \\ drule_all_then assume_tac MEM_procsOf_chor_itree
          \\ iforest_steps_eval
          \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split
          \\ split_updates_tac
          \\ forest_chor_tail_tac)
      >- (qexists_tac ‘[q1;q2;q1;q2]’
          \\ qpat_assum ‘¬MEM q1 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree)
          \\ qpat_assum ‘¬MEM q2 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree)
          \\ iforest_steps_eval
          \\ forest_chor_tail_tac))
QED

Definition sel_path_def:
  sel_path w (Sel p b q c) =
  (if w = p
   then p::q::sel_path w c
   else [])
∧ sel_path _ _ = []
End

Theorem project_ok_MEM_not_nil:
  MEM x (procsOf c) ∧
  project_ok x [] c ⇒
  project' x [] c ≠ Nil
Proof
  Induct_on ‘c’ >>
  rw[procsOf_def,project_def,MEM_nub',dprocsOf_nil,dprocsOf_empty] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[])
QED

Theorem project_NOT_MEM_nil:
  ¬MEM x (procsOf c) ∧ dvarsOf c = [] ⇒
  project x [] c = (T,Nil)
Proof
  Induct_on ‘c’ >>
  rw[procsOf_def,project_def,MEM_nub',dprocsOf_nil,dprocsOf_empty,dvarsOf_def,nub'_nil] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  imp_res_tac split_sel_nonproc_NONE >>
  gvs[]
QED

Definition consumes_sel_path_def:
  consumes_sel_path p q (Sel p1 b p2 c1) s it =
  (if p1 = p ∧ p2 = q then
    ∃f. (it = Vis (Select p1) f) ∧
        consumes_sel_path p q c1 s (f (Branch b))
   else if p1 = p then
     consumes_sel_path p q c1 s it
   else
     it = ↑ (chor_itree q s (Sel p1 b p2 c1))
    ) ∧
  consumes_sel_path p q c1 s it = (it = ↑ (chor_itree q s c1))
End

Theorem iforest_steps_chor_true_lemma:
  ∀procs q c1 ψ todo_list.
    iforest_chor_upd_act ψ ∧
    ψ.st = FEMPTY ∧
    compile_network_ok s c1 procs ∧
    iforest_get ψ q = SOME(↑ (chor_itree q (projectS q s) c1)) ∧
    todo_list = FILTER ($≠ q) (sel_path q c1) ∧
    set(procsOf c1) ⊆ set procs ∧
    ALL_DISTINCT procs ∧
    FDOM(ψ.forest) = set procs ∧
    (∀p. MEM p procs ∧ p ≠ q ⇒ ∃t. iforest_get ψ p = SOME t ∧ consumes_sel_path q p c1 (projectS p s) t) ⇒
    ∃ψ'. iforest_steps (sel_path q c1) ψ = SOME ψ' ∧
         iforest_chor_upd_act ψ' ∧ ψ'.st = FEMPTY ∧
         FDOM(ψ'.forest) = set procs ∧
         ∀p. MEM p procs ⇒ iforest_get ψ' p = SOME(↑ (chor_itree p (projectS p s) (cut_sel_upto q c1)))
Proof
  strip_tac >>
  simp[iforest_get_def] >>
  recInduct sel_path_ind >> rw[sel_path_def]
  >- (gvs[procsOf_def,set_nub',consumes_sel_path_def] >>
      imp_res_tac compile_network_ok_dest_sel' >>
      imp_res_tac compile_network_ok_dest_sel >>
      qpat_assum ‘iforest_chor_upd_act _’ (strip_assume_tac o REWRITE_RULE[iforest_chor_upd_act_def]) >>
      simp[SimpL ``$/\``, iforest_steps_def,iforest_can_act_def,chor_itree_def,IS_SOME_EXISTS,iforest_step_def,iforest_upd_def,FLOOKUP_UPDATE,iforest_get_def,libTheory.the_def] >>
      first_assum drule >>
      impl_tac >- simp[] >>
      strip_tac >>
      gvs[] >>
      simp[FLOOKUP_UPDATE] >>
      qmatch_goalsub_abbrev_tac ‘iforest_steps _ ψ'’ >>
      last_x_assum(qspec_then ‘ψ'’ mp_tac) >>
      impl_tac >-
       (simp[Abbr ‘ψ'’,iforest_chor_upd_act_def,FLOOKUP_UPDATE] >>
        rw[cut_sel_upto_def] >>
        gvs[] >>
        simp[SET_EQ_SUBSET,SUBSET_DEF] >>
        first_x_assum drule_all >>
        strip_tac >>
        gvs[]) >>
      simp[cut_sel_upto_def]) >>
  simp[cut_sel_upto_def,iforest_steps_def] >>
  rpt strip_tac >>
  rename1 ‘MEM _ procs ∧ _ ≠ qq’ >>
  rename1 ‘FLOOKUP _ pp’ >>
  Cases_on ‘pp = qq’ >- simp[] >>
  res_tac >>
  gvs[consumes_sel_path_def]
QED

Theorem chor_itree_merge_id:
  chor_itree_merge t t = t
Proof
  simp[Once itree_bisimulation] >>
  qexists_tac ‘λt1 t2. t1 = chor_itree_merge t2 t2 ∨ t1 = t2’ >>
  rw[] >>
  Cases_on ‘t’ >> gvs[chor_itree_merge_def] >>
  rename1 ‘chor_itree_merge(Ret ret)’ >> Cases_on ‘ret’ >> gvs[chor_itree_merge_def]
QED

Theorem itree_eqn_chor_itree_merge:
  ∀n x l r.
    itree_eqn n x l ∧
    itree_eqn n x r ⇒
    itree_eqn n x (chor_itree_merge l r)
Proof
  Induct \\ rw[itree_eqn_def]
  \\ Cases_on ‘x’ \\ Cases_on ‘l’ \\ Cases_on ‘r’
  \\ gvs[itree_eqn_def,chor_itree_merge_def]
  \\ Cases_on ‘x’ \\ rw[itree_eqn_def,chor_itree_merge_def]
QED

Theorem itree_eqn_lift_chor_itree_merge:
  ∀n x l r.
    itree_eqn n x (↑ l) ∧
    itree_eqn n x (↑ r) ⇒
    itree_eqn n x (↑ (chor_itree_merge l r))
Proof
  Induct \\ rw[itree_eqn_def]
  \\ Cases_on ‘x’ \\ Cases_on ‘l’ \\ Cases_on ‘r’
  \\ gvs[itree_eqn_def,chor_itree_merge_def]
  \\ Cases_on ‘x’
  \\ gvs[itree_eqn_def,chor_itree_merge_def]
  \\ Cases_on ‘x''’
  \\ gvs[itree_eqn_def,chor_itree_merge_def]
QED


Theorem itree_eqn_chor_itree_merge_eq:
  ∀n l1 l2 r1 r2.
    itree_eqn n l1 l2 ∧
    itree_eqn n r1 r2 ⇒
    itree_eqn n (chor_itree_merge l1 r1) (chor_itree_merge l2 r2)
Proof
  Induct \\ rw[itree_eqn_def]
  \\ Cases_on ‘l1’ \\ Cases_on ‘r1’
  \\ Cases_on ‘l2’ \\ Cases_on ‘r2’
  \\ gvs[itree_eqn_def,chor_itree_merge_def]
  \\ TRY (Cases_on ‘x’)
  \\ TRY (Cases_on ‘x'’)
  \\ rw[itree_eqn_def,chor_itree_merge_def,itree_eqn_refl]
QED

Theorem itree_eqn_chor_itree_merge_id:
  ∀n l1 l2 r.
    itree_eqn n l1 l2 ∧
    itree_eqn n l1 r ⇒
    itree_eqn n (chor_itree_merge l1 l2) r
Proof
  Induct \\ rw[itree_eqn_def]
  \\ Cases_on ‘l1’
  \\ Cases_on ‘r’
  \\ Cases_on ‘l2’
  \\ gvs[itree_eqn_def,chor_itree_merge_def]
  \\ Cases_on ‘x’
  \\ rw[itree_eqn_def,chor_itree_merge_def,itree_eqn_refl]
QED

Theorem itree_eqn_lift_chor_itree_merge_id:
  ∀n l1 l2 r.
    itree_eqn n (↑l1) (↑l2) ∧
    itree_eqn n (↑l1) r ⇒
    itree_eqn n (↑ (chor_itree_merge l1 l2)) r
Proof
  Induct \\ rw[itree_eqn_def]
  \\ Cases_on ‘l1’
  \\ Cases_on ‘r’
  \\ Cases_on ‘l2’
  \\ gvs[itree_eqn_def,chor_itree_merge_def]
  \\ Cases_on ‘x’
  \\ gvs[itree_eqn_def,chor_itree_merge_def,itree_eqn_refl]
  \\ Cases_on ‘x''’
  \\ gvs[itree_eqn_def,chor_itree_merge_def,itree_eqn_refl]
QED

Theorem project_eq:
  project_ok p lv l ∧
  project_ok p rv r ∧
  project' p lv l = project' p rv r ⇒
  project p lv l = project p rv r
Proof
  rw[]
  \\ qmatch_goalsub_abbrev_tac ‘a = b’
  \\ PairCases_on ‘a’
  \\ PairCases_on ‘b’
  \\ rw[] \\ gs[]
QED

Theorem project_eq':
  project_ok p lv l ∧
  b ∧
  project' p lv l = x ⇒
  project p lv l = (b,x)
Proof
  rw[]
  \\ qmatch_goalsub_abbrev_tac ‘a = _’
  \\ PairCases_on ‘a’
  \\ rw[] \\ gs[]
QED

Theorem split_sel_dvars_nil:
  ∀proc p c b r dl. split_sel proc p c = SOME (b,r) ∧ dvarsOf c = dl ⇒  dvarsOf r = dl
Proof
  rw[] \\ drule split_sel_dvars
  \\ disch_then (assume_tac o GSYM)
  \\ simp[]
QED

fun project_tac l = (first_x_assum (qspecl_then l
                                    (assume_tac o SIMP_RULE std_ss [chor_itree_def]))
                     \\ (NOT_EVERY |> SPEC_ALL
                       |> EQ_IMP_RULE
                       |> snd
                       |> drule_then assume_tac
                       |> TRY)
                     \\ gvs[]
                     \\ (pop_assum irule \\ itree_simp
                         \\ gvs[dprocsOf_MEM_eq])
                        ORELSE (MAP_EVERY imp_res_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge]
                                \\ gvs[itree_eqn_trans,itree_eqn_sym,itree_eqn_merge]))

val project_full_tac = (TRY (qmatch_asmsub_rename_tac ‘(Send pp2 vv2 (project' _ [] next_c))’
                                \\ project_tac [‘Com p vv2 pp2 vv next_c’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac ‘(Receive pp2 vv2 (project' _ [] next_c))’
                                \\ project_tac [‘Com pp2 vv p vv2 next_c’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac ‘(Let vv2 ff2 vss2 (project' _ [] next_c))’
                                \\ project_tac [‘Let vv2 p ff2 vss2 next_c’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac
                                ‘(IfThen vv2 (project' _ [] next_c1) (project' _ [] next_c2))’
                                \\ project_tac [‘IfThen vv2 p next_c1 next_c2’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac
                                ‘(ExtChoice pp2 (project' _ [] next_r1) (project' _ [] next_r2))’
                                \\ qmatch_asmsub_rename_tac ‘split_sel p pp2 next_c2 = SOME (_,next_r2)’
                                \\ qmatch_asmsub_rename_tac ‘split_sel p pp2 next_c1 = SOME (_,next_r1)’
                                \\ project_tac [‘IfThen vv pp2 next_c1 next_c2’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac ‘(IntChoice bb pp2 (project' _ [] next_c))’
                                \\ project_tac [‘Sel p bb pp2 next_c’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac ‘(ExtChoice pp2 (project' _ [] next_c) Nil)’
                                \\ project_tac [‘Sel pp2 T p next_c’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac ‘(ExtChoice pp2 Nil (project' _ [] next_c))’
                                \\ project_tac [‘Sel pp2 F p next_c’,‘s’] \\ NO_TAC)
                        \\ TRY (qmatch_asmsub_rename_tac ‘(Fix ddn (project' _ _ next_c))’
                                \\ project_tac [‘Fix ddn next_c’,‘s’] \\ NO_TAC)
                        \\ TRY (project_tac [‘Nil’,‘s’] \\ NO_TAC))

fun project_merge_tac l = (irule itree_eqn_sym
                           \\ gvs[PULL_FORALL]
                           \\ first_x_assum
                              (qspecl_then l (mp_tac o SIMP_RULE std_ss [chor_itree_def]))
                           \\ first_x_assum
                              (qspecl_then l (mp_tac o SIMP_RULE std_ss [chor_itree_def]))
                           \\ (NOT_EVERY |> SPEC_ALL
                                         |> EQ_IMP_RULE
                                         |> snd
                                         |> drule_then assume_tac
                                         |> TRY)
                           \\ rw []
                           \\ irule itree_eqn_lift_chor_itree_merge
                           \\ simp[project_def,itree_eqn_sym]
                           \\ itree_simp
                           \\ gvs[dprocsOf_MEM_eq,itree_eqn_sym])

Theorem chor_itree_merge_split_sel:
  ∀p q c1 s b r.
    p ≠ q ∧
    split_sel p q c1 = SOME (b,r) ⇒
    chor_itree p s c1 = chor_itree p s (Sel q b p r)
Proof
  recInduct split_sel_ind >>
  rw[split_sel_def] >>
  gvs[chor_itree_def]
QED

val lone_sel_tac = (imp_res_tac chor_itree_merge_split_sel \\ gvs[]
                    \\ itree_simp
                    \\ Cases_on ‘a’
                    \\ itree_simp
                    \\ TRY (first_x_assum irule \\ simp[project_eq]
                            \\ imp_res_tac split_sel_dvars_nil
                            \\ simp []
                            \\ NO_TAC)
                    \\ TRY (irule itree_eqn_trans
                            \\ first_x_assum (irule_at Any)
                            \\ qexists_tac ‘Nil’
                            \\ itree_simp
                            \\ simp[project_eq']
                            \\ imp_res_tac split_sel_dvars_nil
                            \\ simp []
                            \\ NO_TAC))

Theorem chor_itree_project_eq:
  ∀p c1 c2 s.
    dvarsOf c1 = [] ∧
    dvarsOf c2 = [] ∧
    project_ok p [] c2 ∧
    project p [] c1 = project p [] c2 ⇒
    ↑ (chor_itree p s c1) = ↑(chor_itree p s c2)
Proof
  simp[GSYM itree_depth_eqv_eq,itree_depth_eqv_def]
  \\ simp[PULL_FORALL]
  \\ Induct_on ‘n’
  >- rw[itree_eqn_def]
  \\ rpt(GEN_TAC)
  \\ qmatch_goalsub_abbrev_tac ‘project_ok p dvars _’
  \\ ‘dvars = []’ by simp[Abbr‘dvars’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘s’,‘c2’,‘c1’,‘dvars’,‘p’]
  \\ ho_match_mp_tac project_ind
  \\ rpt(conj_tac)
  \\ rpt(GEN_TAC)
  \\ simp[PULL_FORALL]
  >- (MAP_EVERY qid_spec_tac [‘c2’,‘dvars'’,‘p’]
      \\ ho_match_mp_tac project_ind
      \\ rw[Abbr‘dvars’] \\ itree_simp
      \\ EVERY_CASE_TAC
      \\ gvs[dprocsOf_MEM_eq]
      \\ rw [itree_eqn_chor_itree_merge,itree_eqn_sym,itree_eqn_def]
      \\ metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge])
  >- (GEN_TAC \\ GEN_TAC
      \\ MAP_EVERY qid_spec_tac [‘c2’,‘dvars'’,‘p’]
      \\ ho_match_mp_tac project_ind
      \\ rw[Abbr‘dvars’] \\ itree_simp
      \\ EVERY_CASE_TAC
      \\ gvs[dprocsOf_MEM_eq]
      \\ rw [itree_eqn_chor_itree_merge,itree_eqn_sym,itree_eqn_def]
      \\ project_full_tac
      >- (Cases_on ‘a’ \\ simp[itree_eqn_refl]
          \\ first_x_assum irule \\ simp[]
          \\ simp[project_eq])
      >- (Cases_on ‘a’ \\ simp[itree_eqn_refl]
          \\ first_x_assum irule \\ simp[]
          \\ simp[project_eq])
      >- (first_assum (qspecl_then [‘c2’,‘s’] mp_tac)
          \\ impl_tac >- simp[]
          \\ first_assum (qspecl_then [‘c2'’,‘s’] mp_tac)
          \\ impl_tac >- simp[]
          \\ metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge]))
  >- (GEN_TAC \\ GEN_TAC
      \\ MAP_EVERY qid_spec_tac [‘c2’,‘dvars'’,‘p’]
      \\ ho_match_mp_tac project_ind
      \\ rw[Abbr‘dvars’] \\ itree_simp
      \\ EVERY_CASE_TAC
      \\ gvs[dprocsOf_MEM_eq]
      \\ rw [itree_eqn_chor_itree_merge,itree_eqn_sym,itree_eqn_def]
      \\ project_full_tac
      >- (first_x_assum irule \\ simp[project_eq])
      >- (first_assum (qspecl_then [‘c2’,‘s’] mp_tac)
          \\ impl_tac >- simp[]
          \\ first_assum (qspecl_then [‘c2'’,‘s’] mp_tac)
          \\ impl_tac >- simp[]
          \\ metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge]))
  >- (GEN_TAC \\ GEN_TAC
      \\ MAP_EVERY qid_spec_tac [‘c2’,‘dvars'’,‘p’]
      \\ ho_match_mp_tac project_ind
      \\ rw[Abbr‘dvars’] \\ itree_simp
      \\ EVERY_CASE_TAC
      \\ gvs[dprocsOf_MEM_eq,GSYM PULL_FORALL]
      \\ rw [itree_eqn_chor_itree_merge,itree_eqn_sym,itree_eqn_def]
      >- project_merge_tac [‘Nil’,‘s’]
      >- project_merge_tac [‘Com p dvars'' p2 vv c2'’,‘s’]
      >- project_merge_tac [‘Com p dvars'' p2 vv c2'’,‘s’]
      >- project_merge_tac [‘Com p1' vv  p c2 c2'’,‘s’]
      >- project_merge_tac [‘Let p'' p f vs c2’,‘s’]
      >- project_merge_tac [‘Let p'' p f vs c2’,‘s’]
      >- (first_x_assum irule \\ simp[project_eq])
      >- (metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge])
      >- (first_x_assum irule \\ simp[project_eq])
      >- (metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge])
      >- (metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge])
      >- project_merge_tac [‘IfThen p'' p c2 c2'’,‘s’]
      >- project_merge_tac [‘IfThen p'' p c2 c2'’,‘s’]
      >- project_merge_tac [‘IfThen p'' p c2 c2'’,‘s’]
      >- project_merge_tac [‘IfThen vv p1' c2 c2'’,‘s’]
      >- (first_assum (first_assum o mp_then Any (qspec_then ‘s’ mp_tac) o GSYM)
          \\ impl_tac >- simp[]
          \\ rw[]
          \\ irule itree_eqn_lift_chor_itree_merge_id
          \\ gs[PULL_FORALL,itree_eqn_refl]
          \\ first_x_assum
             (qspecl_then [‘IfThen vv p1' c2 c2'’,‘s’]
              (mp_tac o SIMP_RULE std_ss [chor_itree_def,project_def]))
          \\ simp[dvarsOf_def,nub'_def]
          \\ first_x_assum
             (qspecl_then [‘IfThen vv p1' c2 c2'’,‘s’]
              (mp_tac o SIMP_RULE std_ss [chor_itree_def,project_def]))
          \\ simp[dvarsOf_def,nub'_def])
      >- (irule itree_eqn_lift_chor_itree_merge \\ simp[])
      >- lone_sel_tac
      >- (irule itree_eqn_lift_chor_itree_merge \\ simp[])
      >- lone_sel_tac
      >- (first_assum (first_assum o mp_then Any (qspec_then ‘s’ mp_tac) o GSYM)
          \\ impl_tac >- simp[]
          \\ rw[]
          \\ irule itree_eqn_lift_chor_itree_merge_id
          \\ gs[PULL_FORALL,itree_eqn_refl]
          \\ first_x_assum
             (qspecl_then [‘IfThen vv p1' c2 c2'’,‘s’]
              (mp_tac o SIMP_RULE std_ss [chor_itree_def,project_def]))
          \\ simp[dvarsOf_def,nub'_def]
          \\ first_x_assum
             (qspecl_then [‘IfThen vv p1' c2 c2'’,‘s’]
              (mp_tac o SIMP_RULE std_ss [chor_itree_def,project_def]))
          \\ simp[dvarsOf_def,nub'_def])
      >- lone_sel_tac
      >- lone_sel_tac
      >- project_merge_tac [‘Sel p b p2 c2’,‘s’]
      >- project_merge_tac [‘Sel p1' T p c2’,‘s’]
      >- project_merge_tac [‘Sel p1' F p c2’,‘s’]
      >- lone_sel_tac
      >- lone_sel_tac
      >- lone_sel_tac
      >- lone_sel_tac
      >- project_merge_tac [‘Fix dn c2’,‘s’]
      >- project_merge_tac [‘Nil’,‘s’])
  >- (GEN_TAC \\ GEN_TAC
      \\ MAP_EVERY qid_spec_tac [‘c2’,‘dvars'’,‘p’]
      \\ ho_match_mp_tac project_ind
      \\ rw[Abbr‘dvars’] \\ itree_simp
      \\ EVERY_CASE_TAC
      \\ gvs[dprocsOf_MEM_eq]
      \\ rw [itree_eqn_chor_itree_merge,itree_eqn_sym,itree_eqn_def]
      \\ project_full_tac
      \\ TRY lone_sel_tac
      \\ metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge])
  >- (GEN_TAC \\ GEN_TAC
      \\ MAP_EVERY qid_spec_tac [‘c2’,‘dvars'’,‘p’]
      \\ ho_match_mp_tac project_ind
      \\ rw[Abbr‘dvars’]
      \\ itree_simp
      \\ EVERY_CASE_TAC
      \\ gvs[dprocsOf_MEM_eq]
      \\ rw [itree_eqn_chor_itree_merge,itree_eqn_sym,itree_eqn_def]
      >- metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge]
      >- metis_tac [itree_eqn_trans,itree_eqn_sym,itree_eqn_merge]
      \\ first_x_assum irule
      \\ simp[dsubst_def]
      \\ conj_asm1_tac
      >- (irule project_ok_dsubst \\ itree_simp)
      \\ conj_tac
      >- (irule dvarsOf_dsubst \\ itree_simp)
      \\ conj_tac
      >- (irule dvarsOf_dsubst \\ itree_simp)
      \\ irule project_eq \\ simp[]
      \\ conj_asm1_tac
      >- (irule project_ok_dsubst \\ itree_simp)
      \\ dep_rewrite.DEP_ONCE_REWRITE_TAC [project'_dsubst_commute_nil]
      \\ dep_rewrite.DEP_ONCE_REWRITE_TAC [project'_dsubst_commute_nil]
      \\ conj_tac >- itree_simp
      \\ conj_tac >- itree_simp
      \\ simp[]
      \\ AP_TERM_TAC
      \\ itree_simp
      \\ gvs[procsOf_dprocsOf_MEM])
  >- (MAP_EVERY qid_spec_tac [‘c2’,‘dvars'’,‘p’]
      \\ ho_match_mp_tac project_ind
      \\ rw[Abbr‘dvars’] \\ itree_simp
      \\ EVERY_CASE_TAC
      \\ gvs[dprocsOf_MEM_eq]
      \\ rw [itree_eqn_chor_itree_merge,itree_eqn_sym,itree_eqn_def])
QED

Theorem consumes_path_self:
  ∀p q c1 s.
    p ≠ q ⇒ consumes_sel_path p q c1 s (↑(chor_itree q s c1))
Proof
  ntac 2 strip_tac >>
  Induct_on ‘c1’ >> rw[consumes_sel_path_def] >>
  gvs[chor_itree_def]
QED

Theorem consumes_sel_merge_split_sel:
  ∀p q c1 b r.
    p ≠ q ∧
    split_sel p q c1 = SOME (b,r) ⇒
    consumes_sel_path q p c1 s (Vis (Select q) f) = consumes_sel_path q p r s (f (Branch b))
Proof
  recInduct split_sel_ind >>
  rw[split_sel_def] >>
  gvs[consumes_sel_path_def]
QED

Theorem split_sel_project_sel:
  ∀p q c b r dvars.
     p ≠ q ∧
    split_sel p q c = SOME (b,r) ⇒
    project p dvars c = project p dvars (Sel q b p r)
Proof
  ho_match_mp_tac split_sel_ind
  \\ itree_simp
QED

Theorem itree_eqn_merge_eq:
 ∀l r. ↑ l = ↑ r ⇒ ↑(chor_itree_merge l r) =  (↑ l)
Proof
  rw[GSYM itree_depth_eqv_eq,itree_depth_eqv_def]
  \\ rw[itree_eqn_merge]
QED

Theorem consumes_sel_path_true:
  compile_network_ok s (IfThen v q c1 c2) (procsOf (IfThen v q c1 c2)) ∧
  p ≠ q ∧
  dvarsOf (IfThen v q c1 c2) = [] ∧
  FLOOKUP s (v,q) = SOME [1w] ⇒
  consumes_sel_path q p c1 (projectS p s) (↑(chor_itree p (projectS p s) (IfThen v q c1 c2)))
Proof
  rw[compile_network_ok_project_ok] >>
  ‘project_ok p [] (IfThen v q c1 c2)’
    by(Cases_on ‘MEM p (procsOf (IfThen v q c1 c2))’
       >- res_tac >>
       drule project_NOT_MEM_nil >>
       simp[dvarsOf_def]) >>
  last_x_assum kall_tac >>
  gvs[project_def] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  simp[chor_itree_def]
  >- (gvs[dvarsOf_def,nub'_APPEND,nub'_dvarsOf] >>
      drule_all chor_itree_project_eq >>
      disch_then $ qspec_then ‘projectS p s’ assume_tac >>
      dxrule_all itree_eqn_merge_eq >>
      rw[chor_itree_merge_id] >>
      Cases_on ‘c1’ >> gvs[consumes_sel_path_def,split_sel_def] >>
      rw[] >>
      gvs[chor_itree_def] >>
      simp[consumes_path_self])
  >- (gvs[dvarsOf_def,nub'_APPEND,nub'_dvarsOf] >>
      imp_res_tac split_sel_project_ok >>
      drule_all chor_itree_project_eq >>
      disch_then $ qspec_then ‘projectS p s’ assume_tac >>
      dxrule_all itree_eqn_merge_eq >>
      simp[chor_itree_merge_id] >>
      Cases_on ‘c1’ >> gvs[consumes_sel_path_def,split_sel_def] >>
      rw[] >>
      gvs[chor_itree_def] >>
      simp[consumes_path_self])
  >- (imp_res_tac chor_itree_merge_split_sel >>
      simp[chor_itree_def,chor_itree_merge_def] >>
      drule_all consumes_sel_merge_split_sel >>
      strip_tac >>
      simp[chor_itree_merge_def] >>
      simp[consumes_path_self])
QED

Theorem iforest_steps_cleanup_DRESTRICT:
  ∀l ψ.
    ALL_DISTINCT l ∧
    (∀p. MEM p l ⇒ iforest_get ψ p = SOME(Ret End)) ⇒
    iforest_steps l ψ = SOME(ψ with forest := DRESTRICT ψ.forest (COMPL(set l)))
Proof
  Induct >>
  rw[iforest_steps_def]
  >- rw[iforest_component_equality,fmap_eq_flookup,FLOOKUP_DRESTRICT]
  >- simp[iforest_can_act_def] >>
  simp[iforest_step_def,iforest_del_def] >>
  last_x_assum(dep_rewrite.DEP_ONCE_REWRITE_TAC o single) >>
  simp[iforest_get_def,DOMSUB_FLOOKUP_THM] >>
  rw[iforest_component_equality,fmap_eq_flookup,FLOOKUP_DRESTRICT,
     DOMSUB_FLOOKUP_THM] >>
  metis_tac[iforest_get_def]
QED

Theorem compile_network_ok_procsOf_if:
  compile_network_ok s (IfThen v q c1 c2) (procsOf (IfThen v q c1 c2)) ∧
  dvarsOf(IfThen v q c1 c2) = [] ⇒
  set(procsOf c2) DIFF {q} = set(procsOf c1) DIFF {q}
Proof
  spose_not_then strip_assume_tac >>
  gvs[SET_EQ_SUBSET,SUBSET_DEF,dvarsOf_def,nub'_nil] >>
  drule_all_then strip_assume_tac project_NOT_MEM_nil >>
  gvs[compile_network_ok_project_ok,procsOf_def,MEM_nub',SF DNF_ss] >>
  res_tac >>
  imp_res_tac project_ok_ifL >>
  imp_res_tac project_ok_ifR >>
  drule_then drule project_ok_MEM_not_nil >>
  strip_tac >>
  gvs[project_def] >>
  every_case_tac >> gvs[] >>
  imp_res_tac split_sel_nonproc_NONE >> gvs[]
QED

Theorem procsOf_cut:
  set(procsOf c1) = set(sel_path q c1) ∪ set(procsOf(cut_sel_upto q c1))
Proof
  Induct_on ‘c1’ >> rw[sel_path_def,cut_sel_upto_def,procsOf_def,set_nub'] >>
  gvs[SET_EQ_SUBSET,SUBSET_DEF]
QED

Theorem up_iforests:
  (iforest_step ψ p = ψ')
  ⇒ iforest_step (↑ψ) p = (↑ψ')
Proof
  rw[] >>
  rw[iforest_component_equality] >>
  iforest_simp >>
  rw[up_forest_def,FLOOKUP_FMAP_MAP2] >>
  Cases_on ‘FLOOKUP ψ.forest p’ >>
  gvs[] >>
  rename1 ‘↑ t’ >>
  Cases_on ‘t’ >> gvs[] >>
  rw[fmap_eq_flookup] >>
  rw[DOMSUB_FLOOKUP_THM,FLOOKUP_FMAP_MAP2,FLOOKUP_UPDATE] >>
  TOP_CASE_TAC >> gvs[] >>
  rw[FLOOKUP_FMAP_MAP2,FLOOKUP_UPDATE]>>
  Cases_on‘x’ >> gvs[] >>
  rw[DOMSUB_FLOOKUP_NEQ,FLOOKUP_FMAP_MAP2]
QED

Theorem up_iforests_alt:
  iforest_step (↑ψ) p = ↑ $ iforest_step ψ p
Proof
  metis_tac[up_iforests]
QED

Theorem iforest_get_up[simp]:
  iforest_get (↑ψ) p = OPTION_MAP ↑ (iforest_get ψ p)
Proof
  rw[iforest_get_def,AllCaseEqs(),up_forest_def,FLOOKUP_FMAP_MAP2,ETA_AX]
QED

Theorem iforest_can_act_up[simp]:
  iforest_can_act (↑ψ) p = iforest_can_act ψ p
Proof
  rw[DefnBase.one_line_ify NONE iforest_can_act_def,up_forest_def] >>
  every_case_tac >> gvs[] >>
  Cases_on ‘x'’ >> fs [done_lift_def]
QED

Theorem MEM_procsOf_chor_lift_itree:
  ∀c p s. ¬ MEM p (procsOf c) ∧ dvarsOf c = [] ⇒ ↑ (chor_itree p s c) = Ret End
Proof
  rw[] \\ Induct_on ‘c’ \\ itree_simp \\ gs[MEM_FILTER,chor_itree_merge_def]
  \\ gvs[GSYM itree_depth_eqv_eq,itree_depth_eqv_def] \\ rw[]
  \\ metis_tac [itree_eqn_sym,itree_eqn_lift_chor_itree_merge]
QED

Theorem iforest_steps_chor_true:
  ∀c1 c2.
    FLOOKUP s (v,q) = SOME [1w] ∧
    dvarsOf (IfThen v q c1 c2) = [] ∧
    compile_network_ok s (IfThen v q c1 c2) (procsOf (IfThen v q c1 c2))
    ⇒ ∃l. iforest_steps (q::sel_path q c1++l) (↑(chor_iforest (IfThen v q c1 c2) s)) =
      SOME (↑ (chor_iforest (cut_sel_upto q c1) s)) ∧ (∀x. MEM x l ⇒ MEM x (q::sel_path q c1))
Proof
  rpt strip_tac >>
  simp[iforest_steps_def,iforest_can_act_def,iforest_get_def] >>
  simp[Once chor_iforest_def] >>
  simp[FLOOKUP_chor_forest,procsOf_def,MEM_nub',chor_itree_def,IS_SOME_EXISTS,
       GSYM lookup_projectS',
       iforest_step_def,iforest_get_def] >>
  simp[Once chor_iforest_def] >>
  simp[Once chor_iforest_def] >>
  simp[FLOOKUP_chor_forest,procsOf_def,MEM_nub',chor_itree_def,IS_SOME_EXISTS,
       GSYM lookup_projectS',iforest_step_def,iforest_get_def] >>
  simp[iforest_set_def] >>
  simp[iforest_steps_APPEND,PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac ‘iforest_steps _ ψ’ >>
  qspecl_then [‘procsOf(IfThen v q c1 c2)’,‘q’,‘c1’,‘ψ’] mp_tac iforest_steps_chor_true_lemma >>
  simp[] >>
  impl_tac >-
   (simp[Abbr ‘ψ’,iforest_chor_upd_act_def,chor_iforest_def] >>
    conj_tac >- simp[up_forest_def] >>
    conj_tac >- simp[up_forest_def] >>
    conj_tac
    >- (gvs[compile_network_ok_project_ok,up_forest_def] >>
        rw[] >> res_tac >> imp_res_tac project_ok_ifL) >>
    simp[iforest_get_def,FLOOKUP_chor_forest,FLOOKUP_UPDATE,procsOf_def,set_nub',
         all_distinct_nub',SUBSET_DEF,SF DNF_ss,up_forest_def,FLOOKUP_FMAP_MAP2] >>
    conj_tac
    >- rw[SET_EQ_SUBSET,SUBSET_DEF,chor_forest_FDOM,MEM_nub',up_forest_def,FMAP_MAP2_THM] >>
    rpt strip_tac >>
    irule_at Any consumes_sel_path_true >>
    asm_exists_tac >> simp[]) >>
  strip_tac >>
  simp[] >>
  qexists_tac ‘FILTER (λx. ¬MEM x (procsOf(cut_sel_upto q c1))) (nub'(q::sel_path q c1))’ >>
  reverse conj_tac >- simp[MEM_FILTER,MEM_nub'] >>
  qmatch_goalsub_abbrev_tac ‘FILTER _ a1’ >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[iforest_steps_cleanup_DRESTRICT] >>
  conj_tac
  >- (simp[Abbr ‘a1’,FILTER_ALL_DISTINCT,all_distinct_nub'] >>
      rw[MEM_FILTER,MEM_nub'] >>
      gvs[procsOf_def,MEM_nub',SF DNF_ss] >>
      gvs[dvarsOf_def,nub'_nil] >>
      metis_tac[MEM_procsOf_chor_lift_itree,dvarsOf_cut_sel_upto,procsOf_cut,IN_UNION]) >>
  simp[chor_iforest_def,iforest_component_equality,up_forest_def] >>
  gvs[iforest_chor_upd_act_def,iforest_get_def] >>
  rw[fmap_eq_flookup,FLOOKUP_DRESTRICT,chor_forest_def,Abbr ‘a1’] >>
  simp[MEM_FILTER,MEM_nub',FLOOKUP_chor_forest] >>
  ‘∀x. MEM x (procsOf(cut_sel_upto q c1)) ⇒ MEM x (procsOf (IfThen v q c1 c2))’
    by(rpt strip_tac >>
       simp[procsOf_def,MEM_nub'] >>
       metis_tac[procsOf_cut,IN_UNION]) >>
  rw[FLOOKUP_FMAP_MAP2] >>
  cheat
  (* Goes wrong from here *)
  (* simp[flookup_thm] >> *)
  (* gvs[] >> *)
  (* simp[procsOf_def,MEM_nub'] >> *)
  (* reverse conj_asm1_tac *)
  (* >- (drule_all compile_network_ok_procsOf_if >> *)
  (*     rw[SET_EQ_SUBSET,SUBSET_DEF] >> *)
  (*     metis_tac[]) >> *)
  (* metis_tac[procsOf_cut,IN_UNION] *)
QED

Theorem iforest_steps_chor_false:
  ∀c1 c2.
    FLOOKUP s (v,q) = SOME x ∧ x ≠ [1w] ∧
    compile_network_ok s (IfThen v q c1 c2) (procsOf (IfThen v q c1 c2))
    ⇒ ∃l. iforest_steps (q::sel_path q c2++l) (chor_iforest (IfThen v q c1 c2) s) =
      SOME (chor_iforest (cut_sel_upto q c2) s) ∧ (∀x. MEM x l ⇒ MEM x (q::sel_path q c2))
Proof
  Induct \\ rw[cut_sel_upto_def,sel_path_def]
  \\ cheat
QED

Theorem cut_sel_upto_idem:
  ∀c. cut_sel_upto (@p. ¬MEM p (procsOf c)) c = c
Proof
  strip_tac \\ SELECT_ELIM_TAC \\ conj_tac
  >- metis_tac[IN_INFINITE_NOT_FINITE,FINITE_LIST_TO_SET,INFINITE_LIST_UNIV] \\
  strip_tac \\
  Induct_on ‘c’ \\
  rw[cut_sel_upto_def,procsOf_def,MEM_nub']
QED

val chor_inv_tac = (gvs[dvarsOf_def,nub'_dvarsOf,no_self_comunication_def]
                    \\ TRY (drule compile_network_ok_dest_com' \\ strip_tac)
                    \\ TRY (drule compile_network_ok_dest_let \\ strip_tac)
                    \\ TRY (drule compile_network_ok_dest_sel \\ strip_tac)
                    \\ TRY (drule no_undefined_vars_com \\ strip_tac)
                    \\ TRY (drule no_undefined_vars_Let \\ strip_tac)
                    \\ TRY (drule no_undefined_vars_sel \\ strip_tac)
                    \\ gvs[lookup_projectS']
                    \\ irule compile_network_ok_subset
                    \\ first_x_assum (irule_at Any)
                    \\ rw[procsOf_def,set_nub',SUBSET_INSERT_RIGHT])


Theorem iforest_steps_up:
  ∀ps ψ ψ'.
    iforest_steps ps (↑ψ) = SOME ψ'
    ⇒ ∃ψ''. iforest_steps ps ψ = SOME ψ'' ∧ (↑ψ'') = ψ'
Proof
  Induct >>
  rw[iforest_steps_def,up_iforests_alt] >>
  res_tac >>
  rw[]
QED

Theorem iforest_up_steps:
  ∀ps ψ ψ'.
    iforest_steps ps ψ = SOME ψ'
    ⇒ iforest_steps ps (↑ψ) = SOME (↑ψ')
Proof
  Induct >> rw[iforest_steps_def,up_iforests_alt]
QED

Theorem chor_steps_chor':
  ∀c s ψ p p0.
    dvarsOf c = [] ∧
    no_undefined_vars (s,c) ∧
    no_self_comunication c ∧
    compile_network_ok s c (procsOf c) ∧
    iforest_step (↑(chor_iforest (cut_sel_upto p0 c) s)) p = ψ ⇒
    ∃l c' s'. iforest_steps l ψ = SOME (↑(chor_iforest c' s')) ∧
              dvarsOf c' = [] ∧ no_undefined_vars (s',c') ∧
              no_self_comunication c' ∧
              compile_network_ok s' c' (procsOf c')
Proof
  cheat
  (* rw[] *)
  (* \\ rpt (pop_assum mp_tac \\ simp [AND_IMP_INTRO]) *)
  (* \\ MAP_EVERY qid_spec_tac [‘s’,‘p’,‘p0’,‘c’] *)
  (* \\ Induct_on ‘c’ \\ rw[cut_sel_upto_def] *)
  (* >- (qexistsl_tac [‘[]’,‘Nil’] \\ iforest_tac[iforest_steps_def] *)
  (*     \\ rw[no_undefined_vars_def,free_variables_def,compile_network_gen_def]) *)
  (* >- (drule no_undefined_FLOOKUP_if \\ rw[] *)
  (*     \\ rename1 ‘chor_iforest (IfThen v q c1 c2) _’ *)
  (*     \\ rename1 ‘chor_iforest _ s’ *)
  (*     \\ reverse (Cases_on ‘iforest_can_act (chor_iforest (IfThen v q c1 c2) s) p’) *)
  (*     >- (gvs[iforest_can_act_step_idem] \\ qexists_tac ‘[]’ *)
  (*         \\ metis_tac[iforest_steps_def]) *)
  (*     \\ drule iforest_can_act_MEM \\ rw[] *)
  (*     \\ reverse (Cases_on ‘p = q’) *)
  (*     >- (gs[] *)
  (*         \\ irule_at Any iforest_steps_middle_swap *)
  (*         \\ rw[iforest_chor_upd_act_chor_iforest] *)
  (*         \\ Cases_on ‘x = [1w]’ \\ gvs[] *)
  (*         >- (last_x_assum (qspecl_then [‘q’,‘p’,‘s’] mp_tac) *)
  (*             \\ impl_tac *)
  (*             >- (gvs[dvarsOf_def,nub'_dvarsOf,no_self_comunication_def,nub'_APPEND,nub'_def] *)
  (*                 \\ conj_tac *)
  (*                 >- (drule no_undefined_vars_if \\ simp[]) *)
  (*                 >- (drule compile_network_if_l *)
  (*                     \\ rw[] *)
  (*                     \\ irule compile_network_ok_subset *)
  (*                     \\ pop_assum (irule_at Any) *)
  (*                     \\ rw[procsOf_def,set_nub',SUBSET_INSERT_RIGHT])) *)
  (*             \\ rw[] *)
  (*             \\ pop_assum (irule_at Any) \\ simp[] *)
  (*             \\ drule iforest_steps_chor_true *)
  (*             \\ disch_then drule \\ rw[] *)
  (*             \\ first_x_assum (irule_at Any) *)
  (*             \\ first_x_assum (irule_at Any) *)
  (*             (* Should be true from something along the lines of: *)
  (*                ‘split_sel p q c = NONE ⇒ ¬MEM sel_path q c’ *)
  (*              *) *)
  (*             \\ cheat) *)
  (*         >- (first_x_assum (qspecl_then [‘q’,‘p’,‘s’] mp_tac) *)
  (*             \\ impl_tac *)
  (*             >- (gvs[dvarsOf_def,nub'_dvarsOf,no_self_comunication_def,nub'_APPEND,nub'_def] *)
  (*                 \\ conj_tac *)
  (*                 >- (drule no_undefined_vars_if \\ simp[]) *)
  (*                 >- (drule compile_network_if_r *)
  (*                     \\ rw[] *)
  (*                     \\ irule compile_network_ok_subset *)
  (*                     \\ pop_assum (irule_at Any) *)
  (*                     \\ rw[procsOf_def,set_nub',SUBSET_INSERT_RIGHT])) *)
  (*             \\ rw[] *)
  (*             \\ pop_assum (irule_at Any) \\ simp[] *)
  (*             \\ drule_all iforest_steps_chor_false \\ rw[] *)
  (*             \\ first_x_assum (irule_at Any) *)
  (*             \\ first_x_assum (irule_at Any) *)
  (*             (* Should be true from something along the lines of: *)
  (*                ‘split_sel p q c = NONE ⇒ ¬MEM sel_path q c’ *)
  (*              *) *)
  (*             \\ cheat)) *)
  (*     >- (Cases_on ‘x = [1w]’ \\ gvs[] *)
  (*         >- (drule_all iforest_steps_chor_true \\ rw[] *)
  (*             \\ gvs[Once iforest_steps_def] *)
  (*             \\ first_x_assum (irule_at Any) *)
  (*             \\ drule no_undefined_vars_if *)
  (*             \\ drule compile_network_if_l *)
  (*             \\ gvs[dvarsOf_def,nub'_APPEND,nub'_dvarsOf,no_self_comunication_def, *)
  (*                    no_undefined_vars_cut_sel_upto,dvarsOf_cut_sel_upto, *)
  (*                    no_self_comunication_cut_sel_upto] *)
  (*             \\ rpt strip_tac *)
  (*             \\ irule compile_network_ok_subset *)
  (*             \\ drule compile_network_ok_cut_sel_upto *)
  (*             \\ disch_then (qspec_then ‘p’ (irule_at Any)) *)
  (*             \\ irule SUBSET_TRANS *)
  (*             \\ irule_at Any procsOf_cut_sel_upto *)
  (*             \\ rw[procsOf_def,set_nub',SUBSET_INSERT_RIGHT]) *)
  (*         >- (drule_all iforest_steps_chor_false \\ rw[] *)
  (*             \\ gvs[Once iforest_steps_def] *)
  (*             \\ first_x_assum (irule_at Any) *)
  (*             \\ drule no_undefined_vars_if *)
  (*             \\ drule compile_network_if_r *)
  (*             \\ gvs[dvarsOf_def,nub'_APPEND,nub'_dvarsOf,no_self_comunication_def, *)
  (*                    no_undefined_vars_cut_sel_upto,dvarsOf_cut_sel_upto, *)
  (*                    no_self_comunication_cut_sel_upto] *)
  (*             \\ rpt strip_tac *)
  (*             \\ irule compile_network_ok_subset *)
  (*             \\ drule compile_network_ok_cut_sel_upto *)
  (*             \\ disch_then (qspec_then ‘p’ (irule_at Any)) *)
  (*             \\ irule SUBSET_TRANS *)
  (*             \\ irule_at Any procsOf_cut_sel_upto *)
  (*             \\ rw[procsOf_def,set_nub',SUBSET_INSERT_RIGHT]))) *)
  (* >~[‘cut_sel_upto p0 c’] *)
  (* >- (first_x_assum irule *)
  (*     \\ gvs[dvarsOf_def,nub'_dvarsOf,no_self_comunication_def,nub'_APPEND,nub'_def] *)
  (*     \\ drule no_undefined_vars_sel \\ rw[] *)
  (*     \\ drule compile_network_ok_dest_sel *)
  (*     \\ rw[] *)
  (*     \\ irule compile_network_ok_subset *)
  (*     \\ pop_assum (irule_at Any) *)
  (*     \\ rw[procsOf_def,set_nub',SUBSET_INSERT_RIGHT]) *)
  (* (* Removes the cut_sel_upto when not needed *) *)
  (* \\ TRY (first_x_assum (qspec_then ‘@p. ¬MEM p (procsOf c)’ *)
  (*                        (fn t => *)
  (*                           rpt (pop_assum mp_tac) *)
  (*                         \\ assume_tac t *)
  (*                         \\ rpt (strip_tac))) *)
  (*         \\ gs[cut_sel_upto_idem]) *)
  (* >- (reverse (Cases_on ‘iforest_can_act (chor_iforest (Com s2 s1 s0 s c) s') p’) *)
  (*     >- (gvs[iforest_can_act_step_idem] \\ qexists_tac ‘[]’ *)
  (*         \\ metis_tac[iforest_steps_def]) *)
  (*     \\ drule iforest_can_act_MEM \\ rw[] *)
  (*     \\ reverse (Cases_on ‘p = s2 ∨ p = s0’) *)
  (*     >- (gs[] *)
  (*         \\ irule_at Any iforest_steps_middle_swap *)
  (*         \\ rw[iforest_chor_upd_act_chor_iforest] *)
  (*         \\ drule no_undefined_FLOOKUP_com \\ rw[] *)
  (*         \\ first_x_assum (qspecl_then [‘p’,‘s' |+ ((s,s0),x)’] mp_tac) *)
  (*         \\ impl_tac *)
  (*         >- (gvs[dvarsOf_def,nub'_dvarsOf,no_self_comunication_def,procsOf_def] *)
  (*             \\ conj_tac *)
  (*             >- (drule no_undefined_vars_com \\ simp[]) *)
  (*             >- (drule compile_network_ok_dest_com *)
  (*                 \\ rw[] *)
  (*                 \\ irule compile_network_ok_subset *)
  (*                 \\ pop_assum (irule_at Any) *)
  (*                 \\ rw[set_nub',SUBSET_INSERT_RIGHT])) *)
  (*         \\ rw[] \\ pop_assum (irule_at Any) \\ simp[] *)
  (*         \\ first_x_assum (irule_at Any) *)
  (*         \\ reverse (rw iforest_thm) *)
  (*         \\ gvs[IS_SOME_EXISTS,no_self_comunication_def] *)
  (*         >- (drule lookup_projectS \\ rw[]) *)
  (*         \\ drule lookup_projectS \\ rw[] *)
  (*         \\ Cases_on ‘MEM s2 (procsOf c)’ *)
  (*         \\ Cases_on ‘MEM s0 (procsOf c)’ *)
  (*         \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*         >- (qexists_tac ‘[s2;s0]’ *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ ‘MEM s2 (FILTER (λy. y ≠ s0) (procsOf c))’ by simp[MEM_FILTER] *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexists_tac ‘[s2;s0;s0]’ *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexists_tac ‘[s2;s0;s2]’ *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexists_tac ‘[s2;s0;s2;s0]’ *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ qpat_assum ‘¬MEM s0 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ qpat_assum ‘¬MEM s2 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ iforest_steps_eval *)
  (*             \\ forest_chor_tail_tac)) *)
  (*     \\ rw iforest_thm *)
  (*     \\ gvs[IS_SOME_EXISTS,no_self_comunication_def] *)
  (*     \\ TRY (drule no_undefined_FLOOKUP_com \\ rw[] *)
  (*             \\ drule lookup_projectS \\ gs[] \\ NO_TAC) *)
  (*     >- (Cases_on ‘MEM p (procsOf c)’ *)
  (*         \\ Cases_on ‘MEM s0 (procsOf c)’ *)
  (*         \\ gs[] *)
  (*         >- (qexistsl_tac [‘[s0]’,‘c’,‘s' |+ ((s,s0),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ ‘MEM p (FILTER (λy. y ≠ s0) (procsOf c))’ by simp[MEM_FILTER] *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[s0;s0]’,‘c’,‘s' |+ ((s,s0),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[s0;p]’,‘c’,‘s' |+ ((s,s0),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[s0;p;s0]’,‘c’,‘s' |+ ((s,s0),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ qpat_assum ‘¬MEM p _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ qpat_assum ‘¬MEM s0 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ iforest_steps_eval *)
  (*             \\ forest_chor_tail_tac)) *)
  (*     >- (Cases_on ‘MEM s2 (procsOf c)’ *)
  (*         \\ Cases_on ‘MEM p (procsOf c)’ *)
  (*         \\ gs[] *)
  (*         >- (qexistsl_tac [‘[s2;p]’,‘c’,‘s' |+ ((s,p),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ ‘MEM s2 (FILTER (λy. y ≠ p) (procsOf c))’ by simp[MEM_FILTER] *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[s2;p;p]’,‘c’,‘s' |+ ((s,p),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[s2;p;s2]’,‘c’,‘s' |+ ((s,p),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[s2;p;s2;p]’,‘c’,‘s' |+ ((s,p),x)’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ qpat_assum ‘¬MEM p _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ qpat_assum ‘¬MEM s2 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ iforest_steps_eval *)
  (*             \\ forest_chor_tail_tac))) *)
  (* (* Let *) *)
  (* >- (rename1 ‘iforest_step (chor_iforest (Let _ q _ _ _) _) p’ *)
  (*     \\ reverse (Cases_on ‘iforest_can_act (chor_iforest (Let s0 q f l c) s') p’) *)
  (*     >- (gvs[iforest_can_act_step_idem] \\ qexists_tac ‘[]’ *)
  (*         \\ metis_tac[iforest_steps_def]) *)
  (*     \\ drule iforest_can_act_MEM \\ rw[] *)
  (*     \\ Cases_on ‘p = q’ *)
  (*     >- (Cases_on ‘MEM p (procsOf c)’ *)
  (*         >- (qexistsl_tac [‘[]’,‘c’, *)
  (*                           ‘s' |+ ((s0,p),f (MAP (THE ∘ FLOOKUP (projectS p s')) l))’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ last_x_assum kall_tac *)
  (*             \\ simp[iforest_steps_def] *)
  (*             \\ iforest_simp *)
  (*             \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE,FLOOKUP_chor_forest,DOMSUB_FLOOKUP_THM] *)
  (*             \\ rw[] *)
  (*             \\ simp[projectS_fupdate] *)
  (*             \\ gvs[MEM_FILTER,chor_itree_def,fupdate_projectS] *)
  (*             \\ gvs[EXISTS_MEM,PULL_EXISTS,no_undefined_vars_def,free_variables_def, *)
  (*                    MEM_MAP,SUBSET_DEF,PULL_EXISTS,SF DNF_ss,FDOM_FLOOKUP] *)
  (*             \\ gvs[lookup_projectS'] *)
  (*             \\ res_tac *)
  (*             \\ gvs[]) *)
  (*         \\ qexistsl_tac [‘[p]’,‘c’, *)
  (*                          ‘s' |+ ((s0,p),f (MAP (THE ∘ FLOOKUP (projectS p s')) l))’] *)
  (*         \\ reverse conj_tac *)
  (*         >- chor_inv_tac *)
  (*         \\ last_x_assum kall_tac *)
  (*         \\ simp[iforest_steps_def] *)
  (*         \\ iforest_simp *)
  (*         \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE,FLOOKUP_chor_forest,DOMSUB_FLOOKUP_THM] *)
  (*         \\ rw[] *)
  (*         \\ simp[projectS_fupdate] *)
  (*         \\ gvs[MEM_FILTER,chor_itree_def,fupdate_projectS] *)
  (*         \\ gvs[EXISTS_MEM,PULL_EXISTS,no_undefined_vars_def,free_variables_def, *)
  (*                MEM_MAP,SUBSET_DEF,PULL_EXISTS,SF DNF_ss,FDOM_FLOOKUP,MEM_procsOf_chor_itree] *)
  (*         \\ gvs[lookup_projectS'] *)
  (*         \\ res_tac *)
  (*         \\ gvs[] *)
  (*         \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE,FLOOKUP_chor_forest,DOMSUB_FLOOKUP_THM] *)
  (*         \\ rw[] *)
  (*         \\ gvs[MEM_FILTER,chor_itree_def,fupdate_projectS]) *)
  (*     \\ reverse $ Cases_on ‘MEM p (procsOf c)’ *)
  (*     >- (dep_rewrite.DEP_ONCE_REWRITE_TAC [MEM_iforest_step_idem] *)
  (*         \\ conj_tac >- (CCONTR_TAC \\ gvs[procsOf_def,MEM_nub']) *)
  (*         \\ qexistsl_tac [‘[]’,‘c’, *)
  (*                          ‘s' |+ ((s0,q),f (MAP (THE ∘ FLOOKUP (projectS q s')) l))’] *)
  (*         \\ reverse conj_tac *)
  (*         >- chor_inv_tac *)
  (*         \\ last_x_assum kall_tac *)
  (*         \\ simp[iforest_steps_def] *)
  (*         \\ iforest_simp *)
  (*         \\ rw[fmap_eq_flookup,FLOOKUP_UPDATE,FLOOKUP_chor_forest,DOMSUB_FLOOKUP_THM] *)
  (*         \\ rw[] *)
  (*         \\ simp[projectS_fupdate] *)
  (*         \\ gvs[MEM_FILTER,chor_itree_def,fupdate_projectS] *)
  (*         \\ gvs[EXISTS_MEM,PULL_EXISTS,no_undefined_vars_def,free_variables_def, *)
  (*                MEM_MAP,SUBSET_DEF,PULL_EXISTS,SF DNF_ss,FDOM_FLOOKUP] *)
  (*         \\ gvs[lookup_projectS'] *)
  (*         \\ res_tac *)
  (*         \\ gvs[]) *)
  (*     \\ gvs $ MEM_FILTER::no_self_comunication_def::itree_thms *)
  (*     \\ Q.REFINE_EXISTS_TAC ‘q::_’ *)
  (*     \\ simp[iforest_steps_def,GSYM CONJ_ASSOC,GSYM PULL_EXISTS] *)
  (*     \\ conj_asm1_tac *)
  (*     >- (last_x_assum kall_tac *)
  (*         \\ rw[FLOOKUP_chor_forest,chor_itree_def] *)
  (*         \\ match_mp_tac iforest_cong_can_act_step *)
  (*         \\ rw[iforest_cong_def,iforest_can_act_def,chor_iforest_def,non_interference_def, *)
  (*               iforest_get_def,chor_iforest_act_def,FLOOKUP_chor_forest, *)
  (*               chor_itree_def,procsOf_def,MEM_nub' *)
  (*              ] *)
  (*         \\ Cases_on ‘e1’ \\ gvs[chor_iforest_act_def,IS_SOME_EXISTS,AllCaseEqs(),PULL_EXISTS] *)
  (*         \\ Cases_on ‘e2’ \\ gvs[chor_iforest_upd_def,FLOOKUP_UPDATE] \\ rw[libTheory.the_def] *)
  (*         \\ every_case_tac \\ gvs[DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]) *)
  (*     \\ Cases_on ‘iforest_can_act (chor_iforest (Let s0 q f l c) s') p’ *)
  (*     >- (dep_rewrite.DEP_ONCE_REWRITE_TAC[iforest_chor_act_swap] *)
  (*         \\ simp[] *)
  (*         \\ rpt conj_tac *)
  (*         >- EVAL_TAC *)
  (*         >- (simp[iforest_can_act_def,chor_iforest_def,iforest_get_def,chor_itree_def, *)
  (*                 chor_forest_def,procsOf_def,nub'_def,FLOOKUP_UPDATE] \\ *)
  (*             rw[]) *)
  (*         \\ Cases_on ‘MEM q (procsOf c)’ *)
  (*         >- (qmatch_goalsub_abbrev_tac ‘iforest_step newconf’ *)
  (*             \\ ‘newconf = (chor_iforest c (s' |+ ((s0,q),f (MAP (THE ∘ FLOOKUP (projectS q s')) l))))’ *)
  (*               by(unabbrev_all_tac \\ *)
  (*                  simp[iforest_can_act_def,chor_iforest_def,iforest_get_def,chor_itree_def, *)
  (*                       chor_forest_def,procsOf_def,nub'_def,FLOOKUP_UPDATE, *)
  (*                       iforest_step_def *)
  (*                      ] \\ *)
  (*                  reverse IF_CASES_TAC *)
  (*                  >- (gvs[EXISTS_MEM,PULL_EXISTS,no_undefined_vars_def,free_variables_def, *)
  (*                          MEM_MAP,SUBSET_DEF,PULL_EXISTS,SF DNF_ss,FDOM_FLOOKUP] *)
  (*                      \\ gvs[lookup_projectS'] *)
  (*                      \\ res_tac *)
  (*                      \\ gvs[]) *)
  (*                  \\ imp_res_tac iforest_can_act_MEM' *)
  (*                  \\ gvs[procsOf_def,MEM_nub'] *)
  (*                  \\ simp[iforest_set_def,fmap_eq_flookup,FLOOKUP_UPDATE,FLOOKUP_chor_forest] *)
  (*                  \\ rw[MEM_FILTER,MEM_nub'] *)
  (*                  \\ simp[fupdate_projectS,projectS_fupdate] *)
  (*                  \\ gvs[chor_itree_def]) *)
  (*             \\ simp[] *)
  (*             \\ unabbrev_all_tac *)
  (*             \\ last_x_assum match_mp_tac *)
  (*             \\ gvs[compile_network_ok_project_ok,project_def,MEM_FILTER,SF DNF_ss] *)
  (*             \\ reverse conj_tac >- metis_tac[] *)
  (*             \\ gvs[no_undefined_vars_def,SUBSET_DEF,free_variables_def,MEM_MAP,SF DNF_ss] *)
  (*             \\ metis_tac[]) *)
  (*         \\ qmatch_goalsub_abbrev_tac ‘iforest_step newconf’ *)
  (*         \\ ‘newconf = <|forest := chor_forest c *)
  (*                                                (s' |+ ((s0,q),f (MAP (THE ∘ FLOOKUP (projectS q s')) l))) *)
  (*                                                (q::procsOf c); *)
  (*                          st := FEMPTY; *)
  (*                          upd := chor_iforest_upd; act := chor_iforest_act|>’ *)
  (*           by(unabbrev_all_tac \\ *)
  (*              simp[iforest_can_act_def,chor_iforest_def,iforest_get_def,chor_itree_def, *)
  (*                   chor_forest_def,procsOf_def,nub'_def,FLOOKUP_UPDATE, *)
  (*                   iforest_step_def *)
  (*                  ] \\ *)
  (*              reverse IF_CASES_TAC *)
  (*              >- (gvs[EXISTS_MEM,PULL_EXISTS,no_undefined_vars_def,free_variables_def, *)
  (*                      MEM_MAP,SUBSET_DEF,PULL_EXISTS,SF DNF_ss,FDOM_FLOOKUP] *)
  (*                  \\ gvs[lookup_projectS'] *)
  (*                  \\ res_tac *)
  (*                  \\ gvs[]) *)
  (*              \\ imp_res_tac iforest_can_act_MEM' *)
  (*              \\ gvs[procsOf_def,MEM_nub'] *)
  (*              \\ simp[iforest_set_def,fmap_eq_flookup,FLOOKUP_UPDATE,FLOOKUP_chor_forest] *)
  (*              \\ rw[MEM_FILTER,MEM_nub'] *)
  (*              \\ simp[fupdate_projectS,projectS_fupdate] *)
  (*              \\ gvs[chor_itree_def]) *)
  (*         \\ simp[] *)
  (*         \\ Q.REFINE_EXISTS_TAC ‘q::_’ *)
  (*         \\ simp[iforest_steps_def,GSYM CONJ_ASSOC,GSYM PULL_EXISTS] *)
  (*         \\ conj_asm1_tac *)
  (*         >- (match_mp_tac $ cj 1 iforest_cong_thm *)
  (*             \\ conj_tac *)
  (*             >- (match_mp_tac iforest_chor_upd_act_iforest_cong *)
  (*                 \\ simp[iforest_chor_upd_act_def]) *)
  (*             \\ simp[iforest_can_act_def,iforest_get_def,chor_forest_def, *)
  (*                     FLOOKUP_UPDATE,MEM_procsOf_chor_itree]) *)
  (*         \\ dep_rewrite.DEP_ONCE_REWRITE_TAC[iforest_chor_act_swap] *)
  (*         \\ simp[] *)
  (*         \\ rpt conj_tac *)
  (*         >- EVAL_TAC *)
  (*         >- simp[iforest_can_act_def,iforest_get_def,chor_forest_def,FLOOKUP_UPDATE,MEM_procsOf_chor_itree] *)
  (*         >- (gvs[iforest_can_act_def,iforest_get_def,chor_forest_def,FLOOKUP_UPDATE, *)
  (*                 MEM_procsOf_chor_itree,chor_iforest_def,FLOOKUP_chor_forest,procsOf_def, *)
  (*                 MEM_nub',chor_itree_def,fupdate_projectS]) *)
  (*         \\ qmatch_goalsub_abbrev_tac ‘iforest_step a1’ *)
  (*         \\ ‘a1 = chor_iforest c s'’ *)
  (*            by(unabbrev_all_tac *)
  (*               \\ simp[iforest_step_def,iforest_can_act_def,iforest_get_def,chor_forest_def,FLOOKUP_UPDATE, *)
  (*                       MEM_procsOf_chor_itree,chor_iforest_def,FLOOKUP_chor_forest,procsOf_def, *)
  (*                       MEM_nub',chor_itree_def,fupdate_projectS,iforest_del_def,chor_forest_st_idem] *)
  (*               \\ match_mp_tac DOMSUB_NOT_IN_DOM *)
  (*               \\ simp[chor_forest_FDOM]) *)
  (*         \\ simp[] *)
  (*         \\ first_x_assum kall_tac *)
  (*         \\ unabbrev_all_tac *)
  (*         \\ last_x_assum match_mp_tac *)
  (*         \\ gvs[compile_network_ok_project_ok,project_def,MEM_FILTER,SF DNF_ss, *)
  (*                no_undefined_vars_def,SUBSET_DEF,free_variables_def,MEM_MAP] *)
  (*         \\ rw[] *)
  (*         \\ first_x_assum match_mp_tac *)
  (*         \\ gvs[] *)
  (*         \\ metis_tac[free_variables_procsOf]) *)
  (*     \\ simp[iforest_can_act_step_idem] *)
  (*     \\ simp[iforest_steps_def] *)
  (*     \\ last_x_assum kall_tac *)
  (*     \\ gvs[iforest_can_act_def,iforest_get_def,chor_forest_def,FLOOKUP_UPDATE, *)
  (*            MEM_procsOf_chor_itree,chor_iforest_def,FLOOKUP_chor_forest,procsOf_def, *)
  (*            MEM_nub',chor_itree_def,fupdate_projectS, *)
  (*            nub'_def,iforest_step_def,iforest_get_def,MEM_FILTER]) *)
  (* (* Sel *) *)
  (* >- (rename1 ‘iforest_step (chor_iforest (Sel q1 b q2 c) _) p’ *)
  (*     \\ rename1 ‘iforest_step (chor_iforest _ s) _’ *)
  (*     \\ reverse (Cases_on ‘iforest_can_act (chor_iforest (Sel q1 b q2 c) s) p’) *)
  (*     >- (gvs[iforest_can_act_step_idem] \\ qexists_tac ‘[]’ *)
  (*         \\ metis_tac[iforest_steps_def]) *)
  (*     \\ drule iforest_can_act_MEM \\ rw[] *)
  (*     \\ Cases_on ‘b’ (* This is silly *) *)
  (*     \\ (reverse (Cases_on ‘p = q1 ∨ p = q2’) *)
  (*         >-(gs[] *)
  (*            \\ irule_at Any iforest_steps_middle_swap *)
  (*            \\ rw[iforest_chor_upd_act_chor_iforest] *)
  (*            \\ first_x_assum (qspecl_then [‘p’,‘s’] mp_tac) *)
  (*            \\ impl_tac *)
  (*            >- (gvs[dvarsOf_def,nub'_dvarsOf,no_self_comunication_def,procsOf_def] *)
  (*                \\ conj_tac *)
  (*                >- (drule no_undefined_vars_sel \\ simp[]) *)
  (*                >- (drule compile_network_ok_dest_sel *)
  (*                    \\ rw[] *)
  (*                    \\ irule compile_network_ok_subset *)
  (*                    \\ pop_assum (irule_at Any) *)
  (*                    \\ rw[set_nub',SUBSET_INSERT_RIGHT])) *)
  (*            \\ rw[] \\ pop_assum (irule_at Any) \\ simp[] *)
  (*            \\ first_x_assum (irule_at Any) *)
  (*            \\ reverse (rw iforest_thm) *)
  (*            \\ gvs[IS_SOME_EXISTS,no_self_comunication_def] *)
  (*            \\ Cases_on ‘MEM q1 (procsOf c)’ *)
  (*            \\ Cases_on ‘MEM q2 (procsOf c)’ *)
  (*            \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*            >- (qexists_tac ‘[q1;q2]’ *)
  (*                \\ iforest_steps_eval *)
  (*                \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*                \\ ‘MEM q1 (FILTER (λy. y ≠ q2) (procsOf c))’ by simp[MEM_FILTER] *)
  (*                \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*                \\ split_updates_tac *)
  (*                \\ forest_chor_tail_tac) *)
  (*            >- (qexists_tac ‘[q1;q2;q2]’ *)
  (*                \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*                \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*                \\ iforest_steps_eval *)
  (*                \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*                \\ split_updates_tac *)
  (*                \\ forest_chor_tail_tac) *)
  (*            >- (qexists_tac ‘[q1;q2;q1]’ *)
  (*                \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*                \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*                \\ iforest_steps_eval *)
  (*                \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*                \\ split_updates_tac *)
  (*                \\ forest_chor_tail_tac) *)
  (*            >- (qexists_tac ‘[q1;q2;q1;q2]’ *)
  (*                \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*                \\ qpat_assum ‘¬MEM q1 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*                \\ qpat_assum ‘¬MEM q2 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*                \\ iforest_steps_eval *)
  (*                \\ forest_chor_tail_tac)) *)
  (*     \\ rw iforest_thm *)
  (*     \\ gvs[IS_SOME_EXISTS,no_self_comunication_def] *)
  (*     >- (Cases_on ‘MEM p (procsOf c)’ *)
  (*         \\ Cases_on ‘MEM q2 (procsOf c)’ *)
  (*         \\ gs[] *)
  (*         >- (qexistsl_tac [‘[q2]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ ‘MEM p (FILTER (λy. y ≠ q2) (procsOf c))’ by simp[MEM_FILTER] *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[q2;q2]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[q2;p]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[q2;p;q2]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ qpat_assum ‘¬MEM p _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ qpat_assum ‘¬MEM q2 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ iforest_steps_eval *)
  (*             \\ forest_chor_tail_tac)) *)
  (*     >- (Cases_on ‘MEM q1 (procsOf c)’ *)
  (*         \\ Cases_on ‘MEM p (procsOf c)’ *)
  (*         \\ gs[] *)
  (*         >- (qexistsl_tac [‘[q1;p]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ ‘MEM q1 (FILTER (λy. y ≠ p) (procsOf c))’ by simp[MEM_FILTER] *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ simp[FUPDATE_COMMUTES] *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[q1;p;p]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[q1;p;q1]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ drule_all_then assume_tac MEM_procsOf_chor_itree *)
  (*             \\ iforest_steps_eval *)
  (*             \\ dxrule_then (ONCE_REWRITE_TAC o single) chor_forest_split *)
  (*             \\ split_updates_tac *)
  (*             \\ forest_chor_tail_tac) *)
  (*         >- (qexistsl_tac [‘[q1;p;q1;p]’,‘c’,‘s’] *)
  (*             \\ reverse conj_tac *)
  (*             >- chor_inv_tac *)
  (*             \\ gs[dvarsOf_def,nub'_dvarsOf] *)
  (*             \\ qpat_assum ‘¬MEM p _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ qpat_assum ‘¬MEM q1 _’ (mp_then Any (drule_all_then assume_tac) MEM_procsOf_chor_itree) *)
  (*             \\ iforest_steps_eval *)
  (*             \\ forest_chor_tail_tac)))) *)
  (* >- (reverse (Cases_on ‘iforest_can_act (chor_iforest (Fix s c) s') p’) *)
  (*     >- (gvs[iforest_can_act_step_idem] \\ qexists_tac ‘[]’ *)
  (*         \\ metis_tac[iforest_steps_def]) *)
  (*     \\ drule iforest_can_act_MEM \\ rw[] *)
  (*     \\ qexists_tac ‘FILTER (λx. x ≠ p) (procsOf (Fix s c))’ *)
  (*     \\ qmatch_goalsub_abbrev_tac ‘a1 = _’ *)
  (*     \\ ‘a1 = iforest_steps (p::FILTER (λx. x ≠ p) (procsOf (Fix s c))) (chor_iforest (Fix s c) s')’ *)
  (*       by(unabbrev_all_tac *)
  (*          \\ simp[iforest_steps_def] *)
  (*          \\ iforest_simp *)
  (*          \\ gvs[FLOOKUP_chor_forest,chor_itree_def]) *)
  (*     \\ simp[] *)
  (*     \\ ntac 2 $ pop_assum kall_tac *)
  (*     \\ last_x_assum kall_tac *)
  (*     \\ qexistsl_tac [‘dsubst c s (Fix s c)’,‘s'’] *)
  (*     \\ qmatch_goalsub_abbrev_tac ‘iforest_steps a1’ *)
  (*     \\ ‘ALL_DISTINCT a1’ *)
  (*        by(unabbrev_all_tac *)
  (*           \\ gvs[MEM_FILTER] *)
  (*           \\ match_mp_tac FILTER_ALL_DISTINCT *)
  (*           \\ simp[procsOf_all_distinct]) *)
  (*     \\ reverse conj_tac *)
  (*     >- (gvs[dvarsOf_dsubst,free_variables_dsubst_eq_Fix, *)
  (*             no_undefined_vars_def,free_variables_def, *)
  (*             no_self_comunication_def,no_self_comunication_dsubst] *)
  (*         \\ irule compile_network_ok_subset *)
  (*         \\ simp[GSYM dsubst_procsOf_set_eq_Fix] *)
  (*         \\ gs[procsOf_def,nub'_procsOf] *)
  (*         \\ irule_at Any compile_network_ok_dsubt *)
  (*         \\ simp[] \\ asm_exists_tac \\ simp[]) *)
  (*     \\ simp[chor_iforest_def] *)
  (*     \\ ‘PERM (procsOf (dsubst c s (Fix s c))) (procsOf (Fix s c))’ *)
  (*       by(match_mp_tac PERM_ALL_DISTINCT *)
  (*          \\ rw[procsOf_all_distinct,EQ_IMP_THM,set_procsOf_dsubst_eq,procsOf_def,set_nub']) *)
  (*     \\ drule chor_forest_perm *)
  (*     \\ rw[procsOf_all_distinct] *)
  (*     \\ ‘PERM (procsOf (Fix s c)) a1’ *)
  (*       by(unabbrev_all_tac \\ match_mp_tac PERM_ALL_DISTINCT *)
  (*          \\ rw[procsOf_all_distinct,EQ_IMP_THM,set_procsOf_dsubst_eq,procsOf_def,set_nub',MEM_FILTER,MEM_nub'] *)
  (*          \\ gvs[procsOf_def,MEM_nub']) *)
  (*     \\ qpat_abbrev_tac ‘f1 = chor_forest (Fix _ _) _ _’ *)
  (*     \\ ‘f1 = f1 ⊌ chor_forest (dsubst c s (Fix s c)) s' (FILTER (λx. ¬MEM x a1) (procsOf (Fix s c)))’ *)
  (*        by(rw[Abbr ‘f1’,Abbr ‘a1’,fmap_eq_flookup,FLOOKUP_chor_forest] \\ *)
  (*           rw[FLOOKUP_FUNION,FLOOKUP_chor_forest,MEM_FILTER]) *)
  (*     \\ pop_assum (SUBST_TAC o single) *)
  (*     \\ qunabbrev_tac ‘f1’ *)
  (*     \\ drule chor_forest_perm *)
  (*     \\ simp[GSYM PULL_FORALL] *)
  (*     \\ impl_tac >- simp[procsOf_all_distinct] *)
  (*     \\ disch_then $ REWRITE_TAC o single o Once *)
  (*     \\ ntac 3 $ pop_assum kall_tac *)
  (*     \\ ‘set a1 ⊆ set(procsOf(Fix s c))’ *)
  (*        by(rw[Abbr ‘a1’] \\ gvs[procsOf_def,MEM_nub',SUBSET_DEF,MEM_FILTER]) *)
  (*     \\ qpat_x_assum ‘MEM _ _’ kall_tac *)
  (*     \\ qpat_x_assum ‘Abbrev _’ kall_tac *)
  (*     \\ Induct_on ‘a1’ *)
  (*     >- rw[iforest_steps_def,chor_forest_def] *)
  (*     \\ rw[iforest_can_act_def,iforest_get_def,FLOOKUP_FUNION,FLOOKUP_chor_forest,FLOOKUP_UPDATE,chor_itree_def,iforest_step_def,chor_forest_def,iforest_steps_def,iforest_set_def,iforest_del_def] *)
  (*     \\ gvs[] *)
  (*     \\ qpat_x_assum ‘_ = SOME _’ $ REWRITE_TAC o single o GSYM *)
  (*     \\ AP_TERM_TAC *)
  (*     \\ rw[iforest_component_equality,fmap_eq_flookup,iforest_can_act_def,iforest_get_def,FLOOKUP_FUNION,FLOOKUP_chor_forest,FLOOKUP_UPDATE,chor_itree_def,iforest_step_def,chor_forest_def,iforest_steps_def,iforest_set_def,iforest_del_def,MEM_FILTER] *)
  (*     \\ rw[] *)
  (*     \\ gvs[procsOf_def,MEM_nub',set_nub']) *)
  (* >- gvs[dvarsOf_def] *)
QED

Theorem chor_steps_chor:
  ∀c s ψ p.
    dvarsOf c = [] ∧
    no_undefined_vars (s,c) ∧
    no_self_comunication c ∧
    compile_network_ok s c (procsOf c) ∧
    iforest_step (↑ (chor_iforest c s)) p = ψ ⇒
    ∃l c' s'. iforest_steps l ψ = SOME (↑(chor_iforest c' s')) ∧
              dvarsOf c' = [] ∧ no_undefined_vars (s',c') ∧
              no_self_comunication c' ∧
              compile_network_ok s' c' (procsOf c')
Proof
  rw[]
  \\ irule chor_steps_chor'
  \\ asm_exists_tac \\ simp[]
  \\ qexistsl_tac [‘p’,‘@p. ¬MEM p (procsOf c)’]
  \\ simp[cut_sel_upto_idem]
QED

Theorem chor_steps_chor_no_error:
  ∀c s ψ p.
    dvarsOf c = [] ∧
    no_undefined_vars (s,c) ∧
    no_self_comunication c ∧
    compile_network_ok s c (procsOf c) ∧
    iforest_step (chor_iforest c s) p = ψ ⇒
    ∃l c' s'. iforest_steps_no_error l ψ = SOME (chor_iforest c' s') ∧
              dvarsOf c' = [] ∧ no_undefined_vars (s',c') ∧
              no_self_comunication c' ∧
              compile_network_ok s' c' (procsOf c')
Proof
  cheat
QED

Theorem ae_error_free_chor_iforest:
  ∀p ψ c s.
    dvarsOf c = [] ∧
    no_undefined_vars (s,c) ∧
    no_self_comunication c ∧
    compile_network_ok s c (procsOf c) ∧
    ψ = chor_iforest c s ⇒
    ae_error_free p ψ
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[LEFT_FORALL_IMP_THM] >>
  strip_tac >>
  ho_match_mp_tac ae_error_free_coind >> rw[]
  >- (rw[FLOOKUP_chor_forest,iforest_get_def,chor_iforest_def] >>
      metis_tac[chor_itree_not_error,compile_network_ok_project_ok]) >>
  drule chor_steps_chor_no_error >> ntac 3 $ disch_then drule >>
  disch_then $ qspecl_then [‘iforest_step (chor_iforest c s) p'’,‘p'’] mp_tac >>
  simp[] >>
  strip_tac >>
  first_assum $ irule_at $ Pos hd >>
  irule_at (Pos last) EQ_REFL >>
  simp[]
QED

Theorem chor_iforest_steps_no_error:
    dvarsOf c = [] ∧
    no_undefined_vars (s,c) ∧
    no_self_comunication c ∧
    compile_network_ok s c (procsOf c) ∧
    iforest_steps l (chor_iforest c s) = SOME ψ ⇒
    iforest_get ψ p ≠ SOME(Ret Error)
Proof
  rpt strip_tac >>
  ‘ae_error_free p (chor_iforest c s)’ by metis_tac[ae_error_free_chor_iforest] >>
  drule_at (Pos last) iforest_steps_no_error >>
  simp[iforest_chor_upd_act_chor_iforest] >>
  metis_tac[]
QED

Theorem todo_chor_iforest_step:
  iforest_chor_upd_act (↑ ψ) ∧
  todo_chor l (↑ ψ) ∧
  iforest_can_act (↑ ψ) p
  ⇒ ∃l'. todo_chor l' (iforest_step (↑ ψ) p)
Proof
  rw[todo_chor_def]
  \\ qsuff_tac ‘∃l' c s. iforest_steps (p::l') (↑ ψ) = SOME (↑ $ chor_iforest c s) ∧
                         dvarsOf c = [] ∧ no_undefined_vars (s,c) ∧ no_self_comunication c ∧
                         compile_network_ok s c (procsOf c)’
  >- fs[iforest_steps_def]
  \\ reverse (Cases_on ‘MEM p l’)
  >- (‘iforest_can_act (↑ ψ) p’ by fs []
      \\ drule_all iforest_steps_chor_swap \\ rw[]
      \\ ‘∃y. iforest_step (↑ $ chor_iforest c s) p = y’ by simp[]
      \\ drule_all chor_steps_chor
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
      \\ ‘iforest_can_act (↑ ψ) p’ by fs []
      \\ drule_all iforest_steps_chor_swap
      \\ strip_tac \\ fs[]
      \\ gvs[iforest_steps_def])
QED

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

Theorem iforest_itrees_up:
  iforest_itrees (↑t) = iforest_itrees t
Proof
  fs [up_forest_def,iforest_itrees_def,FMAP_MAP2_def]
QED

Theorem ifrest_run_inv:
  ∀s t.
    iforest_run (↑s) (↑t) ⇒
    ∀l. iforest_chor_upd_act s ∧
        todo_chor l (↑s) ⇒
        iforest_itrees (↑t) = ∅
Proof
  Induct_on ‘iforest_run’ \\ rw []
  >-
   (Cases_on ‘l’ \\ gvs [todo_chor_def,iforest_steps_def]
    \\ fs [chor_iforest_itrees_eq_procOf,iforest_itrees_up]
    \\ CCONTR_TAC
    \\ ‘∃x. MEM x (procsOf c)’ by (Cases_on ‘procsOf c’ \\ fs [] \\ metis_tac [])
    \\ drule iforest_can_act_exists \\ strip_tac
    \\ pop_assum $ qspec_then ‘s'’ strip_assume_tac
    \\ last_x_assum mp_tac \\ rewrite_tac []
    \\ once_rewrite_tac [GSYM iforest_can_act_up]
    \\ simp_tac std_ss []
    \\ asm_rewrite_tac []
    \\ simp [] \\ metis_tac [])
  \\ first_x_assum irule
  \\ rpt conj_tac
  >-
   (drule_then (qspec_then ‘p’ mp_tac) iforest_chor_upd_act_iforest_step
    \\ disch_then $ irule_at Any
    \\ ‘∃t. iforest_step s p = t’ by simp []
    \\ drule up_iforests \\ simp [])
  >- irule_at Any EQ_REFL
  \\ irule todo_chor_iforest_step \\ fs []
  \\ conj_tac
  >- fs [iforest_chor_upd_act_def,up_forest_def]
  \\ first_x_assum $ irule_at Any
QED

Theorem iforest_run_up:
  ∀ψ ψ'. iforest_run ψ ψ' ⇒ iforest_run (↑ψ) (↑ψ')
Proof
  Induct_on ‘iforest_run’ \\ rw []
  \\ simp [Once iforest_run_cases] \\ fs []
  \\ disj2_tac \\ qexists_tac ‘p’ \\ fs []
  \\ ‘∃a. iforest_step ψ p = a’ by simp []
  \\ drule up_iforests \\ rw [] \\ fs []
QED

Theorem finally_empty_chor_iforest:
  dvarsOf c = [] ∧ no_undefined_vars (s,c) ∧
  no_self_comunication c ∧
  compile_network_ok s c (procsOf c) ⇒
  finally_empty (chor_iforest c s)
Proof
  rw [finally_empty_def]
  \\ drule_then assume_tac iforest_run_up
  \\ qsuff_tac ‘iforest_itrees (↑ ψ') = ∅’
  >- fs [up_forest_def,iforest_itrees_def,FMAP_MAP2_THM]
  \\ drule ifrest_run_inv
  \\ disch_then $ qspec_then ‘[]’ irule
  \\ conj_tac
  >- fs [iforest_chor_upd_act_def,up_forest_def,chor_iforest_def]
  \\ fs [todo_chor_def,iforest_steps_def]
  \\ irule_at Any EQ_REFL
  \\ simp []
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
    dvarsOf c = [] ∧ no_undefined_vars (s,c) ∧
    no_self_comunication c ∧
    compile_network_ok s c (procsOf c) ∧
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
  \\ gvs [chor_iforest_itrees_eq_procOf]
  \\ fs [finally_empty_chor_iforest]
QED

val _ = export_theory ()
