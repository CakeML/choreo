open preamble payloadSemTheory payloadLangTheory choreoUtilsTheory payload_closureTheory payloadPropsTheory;
open ConseqConv;

val _ = new_theory "payload_closureProof";

Definition no_undefined_writes_def:
  no_undefined_writes n =
  EVERY (λ(p,s,e). set(written_var_names_endpoint e) ⊆ FDOM s.bindings) (endpoints n)
End

Theorem no_undefined_writes_NPar:
  no_undefined_writes (NPar n1 n2) = (no_undefined_writes n1 ∧ no_undefined_writes n2)
Proof
  rw[no_undefined_writes_def,endpoints_def]
QED

Theorem fix_network_NPar:
  fix_network (NPar n1 n2) = (fix_network n1 ∧ fix_network n2)
Proof
  rw[fix_network_def,endpoints_def]
QED

Theorem compile_network_preservation_send:
  ∀p1 p2 conf p3 d p4.
    conf.payload_size > 0
    ∧ trans conf p1 (LSend p3 d p4) p2
    ⇒ trans conf (compile_network_alt p1) (LSend p3 d p4) (compile_network_alt p2)
Proof
  Induct_on ‘p1’ >>
  rw[Once trans_cases,no_undefined_writes_NPar,compile_network_alt_def] >>
  rw[compile_network_alt_def] >>
  TRY(rename1 ‘NPar’ >> rw[Once trans_cases] >> NO_TAC) >>
  fs[no_undefined_writes_def,endpoints_def] >>
  simp[compile_endpoint_def] >>
  rw[Once trans_cases,PULL_EXISTS] >>
  rw[flookup_update_list_some,ALOOKUP_MAP,written_var_names_endpoint_def,ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,FDOM_FLOOKUP,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,EXISTS_OR_THM]
QED

Theorem compile_network_preservation_receive:
  ∀p1 p2 conf p3 d p4.
    conf.payload_size > 0
    ∧ trans conf p1 (LReceive p3 d p4) p2
    ⇒ trans conf (compile_network_alt p1) (LReceive p3 d p4) (compile_network_alt p2)
Proof
  Induct_on ‘p1’ >>
  rw[Once trans_cases,no_undefined_writes_NPar,compile_network_alt_def] >>
  rw[compile_network_alt_def] >>
  TRY(rename1 ‘NPar’ >> rw[Once trans_cases] >> NO_TAC) >>
  fs[no_undefined_writes_def,endpoints_def] >>
  simp[compile_endpoint_def] >>
  rw[Once trans_cases,PULL_EXISTS] >>
  rw[flookup_update_list_some,ALOOKUP_MAP,written_var_names_endpoint_def,ALOOKUP_NONE,MEM_MAP,MEM_FILTER,MEM_nub',PULL_EXISTS,FDOM_FLOOKUP,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,EXISTS_OR_THM]
QED

(* TODO: Figure out a useful relation to put here *)
Inductive compile_rel:
  ∀x. compile_rel x (x:network)
End

Theorem compile_rel_refl:
  compile_rel x x
Proof
  cheat
QED

Theorem compile_rel_reflI:
  ∀x y. x = y ⇒ compile_rel x y
Proof
  simp[compile_rel_refl]
QED

Theorem ALOOKUP_MAP_CONST_EQ:
  ALOOKUP(MAP (λx. (x,k)) l) x =
  if MEM x l then SOME k else NONE
Proof
  Induct_on ‘l’ >> rw[] >> fs[]
QED

Theorem compile_network_preservation_trans:
  ∀p1 p2 conf.
    conf.payload_size > 0
(*    ∧ no_undefined_writes p1*)
    ∧ fix_network p1
    ∧ reduction conf p1 p2
    ⇒ ∃p3. (reduction conf)^* (compile_network_alt p1) p3 ∧
             compile_rel p3 (compile_network_alt p2)
Proof
  rpt strip_tac
  >> qhdtm_x_assum ‘reduction’ (fn thm => rpt(pop_assum mp_tac) >> assume_tac  thm)
  >> fs[payloadSemTheory.reduction_def]
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> pop_assum mp_tac
  >> MAP_EVERY qid_spec_tac [`p2`,`alpha`,`p1`,‘conf’]
  >> ho_match_mp_tac payloadSemTheory.trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >- ((* trans_com_l *)
      fs[no_undefined_writes_NPar]
      >> MAP_EVERY (drule_all_then strip_assume_tac)
                   [compile_network_preservation_send,
                    compile_network_preservation_receive]
      >> simp[compile_network_alt_def]
      >> drule_all_then strip_assume_tac trans_com_l
      >> fs[GSYM reduction_def]
      >> drule_then strip_assume_tac RTC_SUBSET
      >> goal_assum drule
      >> simp[compile_rel_refl])
  >- ((* trans_com_r *)
      fs[no_undefined_writes_NPar]
      >> MAP_EVERY (drule_all_then strip_assume_tac)
                   [compile_network_preservation_send,
                    compile_network_preservation_receive]
      >> simp[compile_network_alt_def]
      >> drule_all_then strip_assume_tac trans_com_r
      >> fs[GSYM reduction_def]
      >> drule_then strip_assume_tac RTC_SUBSET
      >> goal_assum drule
      >> simp[compile_rel_refl])
  >- ((* trans_dequeue_last_payload *)
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      CONSEQ_CONV_TAC(
        DEPTH_CONSEQ_CONV(
          CONSEQ_REWRITE_CONV
          ([],[compile_rel_reflI],[]))) >>
      fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
         flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
      csimp[CaseEq "bool",written_var_names_endpoint_def])
  >- ((* trans_dequeue_intermediate_payload *)
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      CONSEQ_CONV_TAC(
        DEPTH_CONSEQ_CONV(
          CONSEQ_REWRITE_CONV
          ([],[compile_rel_reflI],[]))) >>
      fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
         flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
      csimp[CaseEq "bool",written_var_names_endpoint_def])
  >- ((* trans_if_true *)
      ‘v ∈ FDOM s.bindings’ by simp[FDOM_FLOOKUP] >>
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      cheat (* different variables initialised *)
      (*CONSEQ_CONV_TAC(
        DEPTH_CONSEQ_CONV(
          CONSEQ_REWRITE_CONV
          ([],[compile_rel_reflI],[]))) >>
      fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
         flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
      csimp[CaseEq "bool",written_var_names_endpoint_def]*))
  >- ((* trans_if_false *)
      ‘v ∈ FDOM s.bindings’ by simp[FDOM_FLOOKUP] >>
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      cheat  (* different variables initialised *))
  >- ((* trans_let *)
      goal_assum (resolve_then (Pos hd) mp_tac RTC_SUBSET) >>
      simp[reduction_def] >>
      simp[compile_network_alt_def,compile_endpoint_def] >>
      simp[Once trans_cases,RIGHT_AND_OVER_OR,PULL_EXISTS,EXISTS_OR_THM] >>
      CONSEQ_CONV_TAC(
        DEPTH_CONSEQ_CONV(
          CONSEQ_REWRITE_CONV
          ([],[compile_rel_reflI],[]))) >>
      fs[state_component_equality,fmap_eq_flookup,FLOOKUP_UPDATE,alookup_distinct_reverse,
         flookup_fupdate_list,MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub'] >>
      csimp[CaseEq "bool",written_var_names_endpoint_def] >>
      fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS,flookup_update_list_some,
         MAP_MAP_o,o_DEF,all_distinct_nub',ALL_DISTINCT_MAP,alookup_distinct_reverse,
         FILTER_ALL_DISTINCT,ALOOKUP_MAP_CONST_EQ,MEM_FILTER,MEM_nub',EXISTS_OR_THM] >>
      conj_tac >- metis_tac[] >>
      AP_TERM_TAC >>
      rw[MAP_EQ_f] >> rw[] >>
      res_tac >>
      fs[FDOM_FLOOKUP])
  >- ((* trans_par_l *)
      fs[compile_network_alt_def,fix_network_NPar]
      >> drule_then (fn thm => goal_assum(resolve_then (Pos hd) mp_tac thm)) payloadPropsTheory.reduction_par_l
      >> cheat (* preserved by parallel *)
     )
  >- ((* trans_par_r *)
      fs[compile_network_alt_def,fix_network_NPar]
      >> drule_then (fn thm => goal_assum(resolve_then (Pos hd) mp_tac thm)) payloadPropsTheory.reduction_par_r
      >> cheat (* preserved by parallel *))
  >- ((* trans_fix *)
      cheat)
  >- ((* trans_Letrec *)
      fs[fix_network_def,endpoints_def,fix_endpoint_def])
  >- ((* trans_call *)
      fs[fix_network_def,endpoints_def,fix_endpoint_def])
QED

Theorem compile_network_preservation:
  ∀conf p1 p2.
    conf.payload_size > 0
    ∧ reduction^* p1 p2 ∧ choice_free_network p1
    ==> (reduction conf)^* (compile_network conf p1) (compile_network conf p2)
Proof
  strip_tac >> simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
  >> strip_tac
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[]
  >> fs[reduction_def]
  >> imp_res_tac choice_free_trans_pres
  >> first_x_assum drule >> strip_tac
  >> fs[GSYM reduction_def]
  >> drule compile_network_preservation_trans >> simp[Once CONJ_SYM]
  >> rpt(disch_then drule) >> strip_tac >> metis_tac[RTC_RTC]
QED

val _ = export_theory ();
