open preamble choreoUtilsTheory
     chorSemTheory chorLangTheory
     chorPropsTheory chorConfluenceTheory;

(*  syncronoush  choreograhies *)
val _ = new_theory "chorSyncProps"

Definition lSyncTrm_def:
  lSyncTrm (s,Nil) l = (s,Nil)
∧ lSyncTrm (s,IfThen v p c1 c2) l = (if FLOOKUP s (v,p) = NONE
                                     then (s,IfThen v p c1 c2)
                                     else if (LTau p v) ⋲ l
                                          then lSyncTrm (syncTrm (s,IfThen v p c1 c2) (LTau p v))
                                                        (l − {|LTau p v|})
                                          else if l = EMPTY_BAG then (s,IfThen v p c1 c2)
                                               else lSyncTrm (chor_tl s (IfThen v p c1 c2)) l)
∧ lSyncTrm (s,c) l   = (if (chor_tag c) ⋲ l
                        then lSyncTrm (syncTrm (s,c) (chor_tag c)) (l − {|chor_tag c|})
                        else if  l = EMPTY_BAG then (s,c)
                             else lSyncTrm (chor_tl s c) l)
Termination
  WF_REL_TAC ‘measure (chor_size o SND o FST)’ \\ rw [chor_tag_def,chor_tl_def]
  \\ rfs [chor_size_def,syncTrm_def,chor_match_def,chor_tl_def]
  >- (Cases_on ‘FLOOKUP s (v,p)’ \\ fs [])
  \\ every_case_tac \\ rw []
  \\ Cases_on ‘FLOOKUP s (v,p)’ \\ fs []
End

(* Alternative induction principle *)
Theorem lSyncTrm_pairind =
  lSyncTrm_ind
  |> Q.SPEC ‘λ(s,c) τ. P s c τ’
  |> SIMP_RULE std_ss []
  |> Q.GEN ‘P’

Theorem trans_lSyncTrm:
  ∀s c l.
   no_self_comunication c ∧ no_undefined_vars (s,c)
   ⇒ trans_sync (s,c) (lSyncTrm (s,c) l)
Proof
  ho_match_mp_tac lSyncTrm_pairind
  \\ rw [lSyncTrm_def,trans_sync_refl,syncTrm_def,chor_tag_def,lrm_def,chor_match_def]
  \\ fs [chor_tl_def]
  \\ TRY (drule_then assume_tac no_undefined_FLOOKUP_if)
  \\ TRY (drule_then assume_tac no_undefined_FLOOKUP_let)
  \\ TRY (drule_then assume_tac no_undefined_FLOOKUP_com)
  \\ fs [no_undefined_vars_def,
         no_self_comunication_def,
         free_variables_def,
         DELETE_SUBSET_INSERT]
  \\ rfs []
  \\ rw [] \\ fs []
  \\ irule trans_sync_step
  \\ metis_tac [trans_rules]
QED

Theorem lcong_PERM:
  ∀l l'. l τ≅ l' ⇒ PERM l l'
Proof
  ho_match_mp_tac lcong_ind
  \\ rw [PERM_SYM]
  >- metis_tac [PERM_TRANS]
  \\ rw [PERM_APPEND_IFF]
  \\ Cases_on ‘t1 = t2’ \\ fs []
  \\ EVAL_TAC \\ rw []
QED

Theorem lSyncTrm_simps:
  ∀p. lSyncTrm p {||} = p
Proof
  Cases \\ Cases_on ‘r’ \\ rw [lSyncTrm_def]
QED

Theorem lcong_LIST_TO_BAG:
  ∀l l'. l τ≅ l' ⇒ LIST_TO_BAG l = LIST_TO_BAG l'
Proof
  rw [] \\ drule_then assume_tac lcong_PERM
  \\ fs [GSYM PERM_LIST_TO_BAG]
QED

Theorem lcong_lSyncTrm:
  ∀l l'. l τ≅ l' ⇒ ∀s c. lSyncTrm (s,c) (LIST_TO_BAG l) = lSyncTrm (s,c) (LIST_TO_BAG l')
Proof
  rw [] \\ drule_then assume_tac lcong_PERM
  \\ fs [GSYM PERM_LIST_TO_BAG]
QED

(* Async trances can not contain LTau *)
Theorem trans_l_not_tau:
  ∀p τ l q. trans p (τ,l) q ⇒ ∀p v. ¬MEM (LTau p v) l
Proof
  rpt (gen_tac)
  \\ Cases_on ‘p’
  \\ Cases_on ‘q’
  \\ MAP_EVERY Q.SPEC_TAC
      (rev [(‘q'’,‘s’),(‘r’,‘c’),(‘τ’,‘τ’),(‘l’,‘l’),(‘q''’,‘s'’),(‘r'’,‘c'’)])
  \\ ho_match_mp_tac trans_pairind
  \\ rw []
QED

(* Async trances can not contain LLet *)
Theorem trans_l_not_let:
  ∀p τ l q. trans p (τ,l) q ⇒ ∀v p f vl. ¬MEM (LLet v p f vl) l
Proof
  rpt (gen_tac)
  \\ Cases_on ‘p’
  \\ Cases_on ‘q’
  \\ MAP_EVERY Q.SPEC_TAC
      (rev [(‘q'’,‘s’),(‘r’,‘c’),(‘τ’,‘τ’),(‘l’,‘l’),(‘q''’,‘s'’),(‘r'’,‘c'’)])
  \\ ho_match_mp_tac trans_pairind
  \\ rw []
QED
(* Tags in the async trace need to be part of the original tag freeprocs (COM) *)
Theorem trans_l_freeprocs_com:
  ∀p τ l q.
   trans p (τ,l) q
   ⇒ ∀c1 v1 c2 v2.
      MEM (LCom c1 v1 c2 v2) l
      ⇒ c1 ∈ freeprocs τ ∨ c2 ∈ freeprocs τ
Proof
  rpt (gen_tac)
  \\ Cases_on ‘p’
  \\ Cases_on ‘q’
  \\ MAP_EVERY Q.SPEC_TAC
      (rev [(‘q'’,‘s’),(‘r’,‘c’),(‘τ’,‘τ’),(‘l’,‘l’),(‘q''’,‘s'’),(‘r'’,‘c'’)])
  \\ ho_match_mp_tac trans_pairind
  \\ rw []
  \\ metis_tac []
QED

(* Tags in the async trace need to be part of the original tag freeprocs (SEL) *)
Theorem trans_l_freeprocs_sel:
  ∀p τ l q.
   trans p (τ,l) q
   ⇒ ∀c1 b c2.
      MEM (LSel c1 b c2) l
      ⇒ c1 ∈ freeprocs τ ∨ c2 ∈ freeprocs τ
Proof
  rpt (gen_tac)
  \\ Cases_on ‘p’
  \\ Cases_on ‘q’
  \\ MAP_EVERY Q.SPEC_TAC
      (rev [(‘q'’,‘s’),(‘r’,‘c’),(‘τ’,‘τ’),(‘l’,‘l’),(‘q''’,‘s'’),(‘r'’,‘c'’)])
  \\ ho_match_mp_tac trans_pairind
  \\ rw []
  \\ metis_tac []
QED

Theorem trans_trans_sync':
  ∀c s τ l s' c'.
   no_self_comunication c  ∧
   no_undefined_vars (s,c) ∧
   trans (s,c) (τ,l) (s',c')
   ⇒ trans_sync (s,c) (lSyncTrm (s',c') (LIST_TO_BAG l))
Proof
  Induct
  >- fs [Once trans_cases]
  \\ rw []
  \\  qpat_x_assum `trans _ _ _`
                   (ASSUME_TAC o SIMP_RULE std_ss [Once trans_cases])
  \\ rw [] >> rfs [] >> rw []
  (* If-Normal *)
  >- (irule trans_sync_step
      \\ MAP_EVERY qexists_tac [‘(s',c)’,‘LTau l s’]
      \\ reverse conj_tac
      >- metis_tac [trans_rules]
      \\ Cases_on ‘c’ \\ fs [lSyncTrm_def,trans_sync_refl])
  (* If-Swap-Sync*)
  >- (irule trans_sync_step
      \\ MAP_EVERY qexists_tac [‘(s',c')’,‘LTau l s’]
      \\ reverse conj_tac
      >- metis_tac [trans_rules]
      \\ Cases_on ‘c'’ \\ fs [lSyncTrm_def,trans_sync_refl])
  (*  If-Swap-Async*)
  >- (rw []
      \\ qpat_assum ‘trans _ _ (s'',_)’ mp_tac
      \\ disch_then (mp_then Any assume_tac trans_state) \\ rveq
      \\ drule_then assume_tac no_undefined_FLOOKUP_if \\ fs []
      \\ rw [lSyncTrm_def]
      >- (Cases_on ‘τ’
          \\ fs [state_from_tag_def,
                 chorSemTheory.freeprocs_def,
                 FLOOKUP_UPDATE] \\ rfs [])
      >- metis_tac [IN_LIST_TO_BAG,trans_l_not_tau]
      >- (rfs [LIST_TO_BAG_EQ_EMPTY] \\ rveq
          \\ fs [lcong_nil_simp]
          \\ irule trans_sync_one \\ qexists_tac ‘τ’
          \\ irule trans_if_swap  \\ fs []
          \\ qexists_tac ‘[]’ \\ fs [lcong_sym])
      \\ Cases_on ‘x = [1w]’ \\ fs []
      \\ ho_match_mp_tac trans_sync_step
      (* True branch *)
      >- (drule_then (qspecl_then [‘c’,‘c'’] assume_tac) trans_if_true
          \\ asm_exists_tac \\ fs []
          \\ qmatch_goalsub_abbrev_tac ‘chor_tl sτ’
          \\ ‘FLOOKUP sτ (s,l) = SOME [1w]’
              by (UNABBREV_ALL_TAC
                  \\ Cases_on ‘τ’
                  \\ fs [state_from_tag_def,
                         chorSemTheory.freeprocs_def,
                         FLOOKUP_UPDATE]
                  \\ rfs [])
          \\ rw [lSyncTrm_def,chor_tl_def]
          \\ first_x_assum irule
          \\ fs [no_self_comunication_def,
                 no_undefined_vars_def,
                 free_variables_def]
          \\ asm_exists_tac \\ fs [])
      (* False branch *)
      \\ drule_then (qspecl_then [‘c’,‘c'’] assume_tac) trans_if_false \\ rfs []
      \\ asm_exists_tac \\ fs []
      \\ qmatch_goalsub_abbrev_tac ‘chor_tl sτ’
      \\ ‘FLOOKUP sτ (s,l) = SOME x ∧ x ≠ [1w]’
          by (UNABBREV_ALL_TAC
              \\ Cases_on ‘τ’
              \\ fs [state_from_tag_def,
                     chorSemTheory.freeprocs_def,
                     FLOOKUP_UPDATE]
              \\ rfs [])
      \\ rw [lSyncTrm_def,chor_tl_def]
      \\ drule_then assume_tac lcong_LIST_TO_BAG \\ fs []
      \\ first_x_assum irule
      \\ fs [no_self_comunication_def,
             no_undefined_vars_def,
             free_variables_def]
      \\ asm_exists_tac \\ fs [])
  (* Com-Normal *)
  >- (irule trans_sync_step
      \\ qmatch_goalsub_abbrev_tac ‘lSyncTrm (s'',_)’
      \\ MAP_EVERY qexists_tac [‘(s'',c)’,‘LCom l0 s0 l s’]
      \\ reverse conj_tac
      >- metis_tac [trans_rules,trans_sync_refl]
      \\ Cases_on ‘c’ \\ fs [lSyncTrm_def,trans_sync_refl])
  (* Com-Swap *)
  >- (drule_then assume_tac trans_state \\ rveq
      \\ drule_then assume_tac no_undefined_FLOOKUP_com \\ fs []
      \\ rw [lSyncTrm_def]
      >- (fs [IN_LIST_TO_BAG,chor_tag_def]
          \\ drule_then drule trans_l_freeprocs_com
          \\ fs [])
      >- (rfs [LIST_TO_BAG_EQ_EMPTY] \\ rveq
          \\ irule trans_sync_one \\ qexists_tac ‘τ’
          \\ irule trans_com_swap  \\ fs [])
      \\ qmatch_goalsub_abbrev_tac ‘chor_tl sτ’
      \\ ‘FLOOKUP sτ (s0,l0) = SOME x’
          by (UNABBREV_ALL_TAC
              \\ Cases_on ‘τ’
              \\ fs [state_from_tag_def,
                     chorSemTheory.freeprocs_def,
                     FLOOKUP_UPDATE]
              \\ rfs [])
      \\ rw [chor_tl_def,FLOOKUP_UPDATE]
      \\ ho_match_mp_tac trans_sync_step
      \\ fs [no_self_comunication_def]
      \\ qspec_then ‘s'’ mp_tac trans_com
      \\ disch_then drule
      \\ disch_then (drule_then (qspecl_then [‘s’,‘c’] assume_tac))
      \\ asm_exists_tac \\ fs []
      \\ first_x_assum irule
      \\ fs [no_undefined_vars_def,
             free_variables_def,
             DELETE_SUBSET_INSERT]
      \\ qexists_tac ‘τ’
      \\ irule semantics_add_irrelevant_state \\ fs [])
  (* Com-Async *)
  >- (rw [lSyncTrm_def,chor_tag_def,syncTrm_def,chor_match_def,chor_tl_def]
      \\ drule_then assume_tac trans_state \\ rveq
      \\ drule_then assume_tac no_undefined_FLOOKUP_com \\ fs [no_self_comunication_def]
      \\ qmatch_goalsub_abbrev_tac ‘FLOOKUP sτ’
      \\ drule_then drule trans_com
      \\ disch_then (qspecl_then [‘s’,‘c’] assume_tac)
      \\ ‘FLOOKUP sτ (s0,l0) = SOME x’
              by (UNABBREV_ALL_TAC
                  \\ Cases_on ‘τ’
                  \\ fs [state_from_tag_def,
                         chorSemTheory.freeprocs_def,
                         chorSemTheory.written_def,
                         FLOOKUP_UPDATE]
                  \\ rfs [])
      \\ ho_match_mp_tac trans_sync_step
      \\ asm_exists_tac \\ fs []
      \\ first_x_assum irule
      \\ fs [no_undefined_vars_def,
             free_variables_def,
             DELETE_SUBSET_INSERT]
      \\ qexists_tac ‘τ’
      \\ irule semantics_add_irrelevant_state2 \\ fs []
      \\ Cases_on ‘τ’
      \\ fs [chorSemTheory.written_def,
             chorSemTheory.read_def,
             chorSemTheory.freeprocs_def] \\ rfs []
      \\ qpat_x_assum ‘l ≠ l'’ mp_tac
      \\ rpt (last_x_assum (K ALL_TAC))
      \\ Induct_on ‘l0'’ \\ fs [])
  (* Let-Normal *)
  >- (irule trans_sync_step
      \\ qmatch_goalsub_abbrev_tac ‘lSyncTrm (s'',_)’
      \\ MAP_EVERY qexists_tac [‘(s'',c)’,‘LLet s l0 f l’]
      \\ reverse conj_tac
      >- metis_tac [trans_rules,trans_sync_refl]
      \\ Cases_on ‘c’ \\ fs [lSyncTrm_def,trans_sync_refl])
  (* Let-Swap *)
  >- (drule_then assume_tac trans_state \\ rveq
     \\ drule_then assume_tac no_undefined_FLOOKUP_let \\ fs []
     \\ rw [lSyncTrm_def]
     >- (fs [IN_LIST_TO_BAG,chor_tag_def]
         \\ metis_tac [trans_l_not_let])
     >- (rfs [LIST_TO_BAG_EQ_EMPTY] \\ rveq
         \\ irule trans_sync_one \\ qexists_tac ‘τ’
         \\ irule trans_let_swap  \\ fs [])
     \\ qmatch_goalsub_abbrev_tac ‘chor_tl sτ’
     \\ rw [chor_tl_def,FLOOKUP_UPDATE]
     \\ ho_match_mp_tac trans_sync_step
     \\ fs [no_self_comunication_def]
     \\ qspec_then ‘s'’ mp_tac trans_let
     \\ disch_then drule
     \\ disch_then (qspecl_then [‘s’,‘f’,‘c’] assume_tac)
     \\ asm_exists_tac \\ fs []
     \\ first_x_assum irule
     \\ fs [no_undefined_vars_def,
            free_variables_def,
            DELETE_SUBSET_INSERT]
     \\ qexists_tac ‘τ’
     \\ qmatch_goalsub_abbrev_tac ‘f s0’
     \\ qmatch_goalsub_abbrev_tac ‘(sτ |+ (_, f s1))’
     \\ ‘s0 = s1’ by
         (UNABBREV_ALL_TAC
          \\ Cases_on ‘τ’
          \\ fs [state_from_tag_def,
                 chorSemTheory.freeprocs_def,
                 FLOOKUP_UPDATE]
          \\ rfs []
          \\ qpat_x_assum ‘l0 ≠ _'’ mp_tac
          \\ rpt (last_x_assum (K ALL_TAC))
          \\ Induct_on ‘l’ \\ rw [] \\ fs [FLOOKUP_UPDATE])
     \\ fs [] \\ irule semantics_add_irrelevant_state2
     \\ fs []
     \\ Cases_on ‘τ’
     \\ fs [chorSemTheory.written_def,
            chorSemTheory.read_def,
            chorSemTheory.freeprocs_def] \\ rfs []
     \\ qpat_x_assum ‘l0 ≠ l''’ mp_tac
     \\ rpt (last_x_assum (K ALL_TAC))
     \\ Induct_on ‘l0'’ \\ fs [])
  (* Sel-Normal *)
  >- (irule trans_sync_step
      \\ qmatch_goalsub_abbrev_tac ‘lSyncTrm (s'',_)’
      \\ MAP_EVERY qexists_tac [‘(s'',c)’,‘LSel l0 b l’]
      \\ reverse conj_tac
      >- metis_tac [trans_rules,trans_sync_refl]
      \\ Cases_on ‘c’ \\ fs [lSyncTrm_def,trans_sync_refl])
  (* Let-Swap *)
  >- (rw [lSyncTrm_def,chor_tag_def,syncTrm_def,chor_match_def,chor_tl_def]
      >- (fs [IN_LIST_TO_BAG,chor_tag_def]
          \\ drule_then drule trans_l_freeprocs_sel
          \\ fs [])
      >- (rfs [LIST_TO_BAG_EQ_EMPTY] \\ rveq
          \\ irule trans_sync_one \\ qexists_tac ‘τ’
          \\ irule trans_sel_swap  \\ fs [])
      \\ ho_match_mp_tac trans_sync_step
      \\ fs [no_self_comunication_def]
      \\ qspec_then ‘s’ mp_tac trans_sel
      \\ disch_then drule
      \\ disch_then (qspecl_then [‘b’,‘c’] assume_tac)
      \\ asm_exists_tac \\ fs []
      \\ first_x_assum irule
      \\ fs [no_undefined_vars_def,
             free_variables_def,
             DELETE_SUBSET_INSERT]
      \\ asm_exists_tac \\ fs [])
  (* Let-Async *)
  \\ rw [lSyncTrm_def,chor_tag_def,syncTrm_def,chor_match_def,chor_tl_def]
  \\ ho_match_mp_tac trans_sync_step
  \\ fs [no_self_comunication_def]
  \\ qspec_then ‘s’ mp_tac trans_sel
  \\ disch_then drule
  \\ disch_then (qspecl_then [‘b’,‘c’] assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ first_x_assum irule
  \\ fs [no_undefined_vars_def,
         free_variables_def,
         DELETE_SUBSET_INSERT]
  \\ asm_exists_tac \\ fs []
QED

Theorem trans_sync_imp_trans_s:
  ∀p q. trans_sync p q ⇒ trans_s p q
Proof
  simp [trans_sync_def,trans_s_def]
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rw [] \\ irule RTC_TRANS
  \\ rw [] \\  metis_tac []
QED

Theorem trans_trans_sync:
  ∀c s τ l s' c'.
   no_self_comunication c  ∧
   no_undefined_vars (s,c) ∧
   trans (s,c) (τ,l) (s',c')
   ⇒ trans_sync (s,c) (lSyncTrm (s',c') (LIST_TO_BAG l)) ∧
     trans_s (s',c') (lSyncTrm (s',c') (LIST_TO_BAG l))
Proof
  rw []
  >- (irule trans_trans_sync' \\ metis_tac [])
  \\ irule trans_sync_imp_trans_s
  \\ irule trans_lSyncTrm
  \\ rw []
  \\ metis_tac [no_self_comunication_trans_pres
               , no_undefined_vars_trans_pres]
QED

(* A linear version of ‘trans_s’ *)
Definition trans_ln_def:
  trans_ln = RTC (λp q. ∃τ. trans p (τ,[]) q ∧ (q = UNCURRY chor_tl p))
End

Inductive trans_l:
  (∀s c. trans_l [] {||} (s,c) (s,c))
∧ (∀s c τ l s' c'.
    trans (s,c) (τ,l) (s',c)
    ⇒ trans_l [τ] (LIST_TO_BAG l) (s,c) (s',c'))
∧ (∀s c τ l s' c'.
   trans_l tl al (s,c) (s',c') ∧ trans (s',c') (τ,l) (s'',c'')
   ⇒ trans_l (tl ++ [τ]) (BAG_MERGE al (LIST_TO_BAG l) − {|τ|}) (s,c) (s'',c''))
End

Theorem trans_ln_step:
  ∀p τ q r.
  trans p (τ,[]) q ∧ q = UNCURRY chor_tl p ∧ trans_ln q r ⇒
  trans_ln p r
Proof
  rw[trans_ln_def] >>
  match_mp_tac(CONJUNCT2 (SPEC_ALL RTC_RULES)) >>
  metis_tac[]
QED

Theorem trans_s_step:
  ∀p τ l q r.
  trans p (τ,l) q ∧ trans_s q r ⇒
  trans_s p r
Proof
  rw[trans_s_def] >>
  match_mp_tac(CONJUNCT2 (SPEC_ALL RTC_RULES)) >>
  metis_tac[]
QED

Theorem trans_trans_ln:
  ∀c s τ l s' c'.
  no_self_comunication c ∧ no_undefined_vars (s,c) ∧
  trans (s,c) (τ,l) (s',c')
  ⇒ ∃s'' c''.
     trans_ln (s,c)  (s'',c'') ∧
     trans_s (s',c') (s'',c'')
Proof
  Induct
  >- fs [Once trans_cases]
  \\ rw []
  \\  qpat_x_assum `trans _ _ _`
                   (ASSUME_TAC o SIMP_RULE std_ss [Once trans_cases])
  \\ rw [] >> rfs [] >> rw []
  (* If-Normal *)
  >- (qexists_tac ‘s'’ >> qexists_tac ‘c’ >>
      simp[trans_s_def] >>
      simp[trans_ln_def] >>
      match_mp_tac RTC_SINGLE >>
      rw[chor_tl_def] >>
      metis_tac[trans_rules])
  >- (qexists_tac ‘s'’ >> qexists_tac ‘c'’ >>
      simp[trans_s_def] >>
      simp[trans_ln_def] >>
      match_mp_tac RTC_SINGLE >>
      rw[chor_tl_def] >>
      metis_tac[trans_rules])
  >- (fs[no_self_comunication_def] >>
      ‘no_undefined_vars (s',c)’ by fs[no_undefined_vars_def,free_variables_def] >>
      ‘no_undefined_vars (s',c')’ by fs[no_undefined_vars_def,free_variables_def] >>
      res_tac >>
      Cases_on ‘FLOOKUP s' (s,l)’
      >- (fs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP]) >>
      drule lookup_fresh_after_trans >> simp[] >>
      disch_then drule >>
      disch_then(qspec_then ‘s’ assume_tac) >>
      rename1 ‘FLOOKUP _ _= SOME d’ >>
      Cases_on ‘d=[1w]’ >-
        (rveq  >>
         rename1 ‘trans_ln (s',c) (sss,ccc)’ >>
         qexists_tac ‘sss’ >> qexists_tac ‘ccc’ >>
         conj_tac >-
           (match_mp_tac trans_ln_step >>
            simp[chor_tl_def] >>
            metis_tac[trans_if_true]) >>
         match_mp_tac trans_s_step >>
         metis_tac[trans_if_true]) >>
      rename1 ‘trans_ln (s',c') (sss,ccc)’ >>
      qexists_tac ‘sss’ >> qexists_tac ‘ccc’ >>
      conj_tac >-
       (match_mp_tac trans_ln_step >>
        simp[chor_tl_def] >>
        metis_tac[trans_if_false]) >>
      match_mp_tac trans_s_step >>
      metis_tac[trans_if_false])
  >- (qexists_tac ‘s' |+ ((s,l),d)’ >>
      qexists_tac ‘c’ >>
      simp[trans_s_def] >>
      simp[trans_ln_def] >>
      match_mp_tac RTC_SINGLE >>
      simp[chor_tl_def] >>
      metis_tac[trans_rules])
  >- (fs[no_self_comunication_def] >>
      ‘∃d. FLOOKUP s' (s0,l0) = SOME d’
        by(fs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP]) >>
      ‘no_undefined_vars (s' |+ ((s,l),d),c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM] >>
           metis_tac[]) >>
      drule lookup_fresh_after_trans >> simp[] >>
      disch_then(qspecl_then [‘l0’,‘s0’] mp_tac) >> rw[] >>
      drule semantics_add_irrelevant_state >> simp[] >> disch_then drule >>
      disch_then(qspecl_then [‘s’,‘d’] assume_tac) >>
      first_x_assum(drule_all_then strip_assume_tac) >>
      rename1 ‘trans_ln (s' |+ _,c) (sss,ccc)’ >>
      qexists_tac ‘sss’ >> qexists_tac ‘ccc’ >>
      conj_tac >-
        (match_mp_tac trans_ln_step >> simp[chor_tl_def] >>
         metis_tac[trans_com]) >>
      match_mp_tac trans_s_step >>
      metis_tac[trans_com])
  >- (fs[no_self_comunication_def] >>
      ‘∃d. FLOOKUP s' (s0,l0) = SOME d’
        by(fs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP]) >>
      ‘no_undefined_vars (s' |+ ((s,l),d),c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM] >>
           metis_tac[]) >>
      drule_all_then assume_tac lookup_unwritten_after_trans_tup >>
      drule_then drule semantics_add_irrelevant_state_tup >>
      disch_then(qspecl_then [‘s’,‘d’] mp_tac) >> rw[] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      rename1 ‘trans_ln (s' |+ _,c) (sss,ccc)’ >>
      qexists_tac ‘sss’ >> qexists_tac ‘ccc’ >>
      conj_tac >-
        (match_mp_tac trans_ln_step >> simp[chor_tl_def] >>
         metis_tac[trans_com]) >>
      match_mp_tac trans_s_step >>
      metis_tac[trans_com])
  >- (qexists_tac ‘s' |+ ((s,l0),f (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,l0)) l)))’ >>
      qexists_tac ‘c’ >>
      simp[trans_s_def] >>
      simp[trans_ln_def] >>
      match_mp_tac RTC_SINGLE >>
      rw[chor_tl_def] >>
      metis_tac[trans_rules])
  >- (fs[no_self_comunication_def] >>
      ‘no_undefined_vars (s' |+ ((s,l0),f (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,l0)) l))),c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,
              DISJ_IMP_THM,FORALL_AND_THM] >>
           metis_tac[]) >>
      drule_then assume_tac no_undefined_FLOOKUP_let >>
      drule_then drule map_lookup_fresh_after_trans_tup >>
      disch_then(qspec_then ‘l’ assume_tac) >>
      drule semantics_add_irrelevant_state >> simp[] >> disch_then drule >>
      disch_then(qspecl_then [‘s’,‘f (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,l0)) l))’] mp_tac) >>
      strip_tac >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      rename1 ‘trans_ln (s' |+ _,c) (sss,ccc)’ >>
      qexists_tac ‘sss’ >> qexists_tac ‘ccc’ >>
      conj_tac >-
        (match_mp_tac trans_ln_step >> simp[chor_tl_def] >>
         metis_tac[trans_let]) >>
      match_mp_tac trans_s_step >>
      simp[Once CONJ_SYM] >> goal_assum drule >>
      qexists_tac ‘LLet s l0 f l’ >> qexists_tac ‘[]’ >>
      qpat_x_assum ‘MAP _ _ = MAP _ _’ (assume_tac o GSYM) >>
      simp[] >>
      match_mp_tac trans_let >>
      fs[EVERY_MEM,IS_SOME_EXISTS,MEM_MAP,PULL_EXISTS] >>
      rw[] >> res_tac >>
      metis_tac[lookup_fresh_after_trans,FST])
  >- (qexists_tac ‘s’ >> qexists_tac ‘c’ >>
      simp[trans_s_def] >>
      simp[trans_ln_def] >>
      match_mp_tac RTC_SINGLE >>
      rw[chor_tl_def] >>
      metis_tac[trans_rules])
  >- (fs[no_self_comunication_def] >>
      ‘no_undefined_vars (s,c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM] >>
           metis_tac[]) >>
      first_x_assum(drule_all_then strip_assume_tac) >>
      rename1 ‘trans_ln (s,c) (sss,ccc)’ >>
      qexists_tac ‘sss’ >> qexists_tac ‘ccc’ >>
      conj_tac >-
        (match_mp_tac trans_ln_step >> simp[chor_tl_def] >>
         metis_tac[trans_sel]) >>
      match_mp_tac trans_s_step >>
      metis_tac[trans_sel])
  >- (fs[no_self_comunication_def] >>
      ‘no_undefined_vars (s,c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM] >>
           metis_tac[]) >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      rename1 ‘trans_ln (s,c) (sss,ccc)’ >>
      qexists_tac ‘sss’ >> qexists_tac ‘ccc’ >>
      conj_tac >-
        (match_mp_tac trans_ln_step >> simp[chor_tl_def] >>
         metis_tac[trans_sel]) >>
      match_mp_tac trans_s_step >>
      metis_tac[trans_sel])
QED

Theorem trans_ln_elim:
  trans_ln sc sc' ⇒ (sc = sc' ∨ trans_ln (UNCURRY chor_tl sc) sc')
Proof
  rw[trans_ln_def,Once RTC_cases] >>
  metis_tac[]
QED

Theorem trans_s_NIL:
  ∀s sc. trans_s (s,Nil) sc ⇒ sc = (s,Nil)
Proof
  strip_tac >>
  ‘∀sc sc'. (sc = (s,Nil)) ∧ (trans_s sc sc') ⇒ (sc' = (s,Nil))’
    by(PURE_ONCE_REWRITE_TAC[trans_s_def] >>
       ho_match_mp_tac RTC_lifts_invariants >>
       rw[Once trans_cases] >>
       fs[]) >>
  metis_tac[PAIR,FST,SND]
QED

Theorem trans_ln_IMP_trans_s:
  ∀a b. trans_ln a b ⇒ trans_s a b
Proof
  simp[trans_ln_def,trans_s_def] >> rpt GEN_TAC >>
  match_mp_tac RTC_MONOTONE >> metis_tac[]
QED

Theorem trans_ln_trans_ln:
  trans_ln a b ∧ trans_ln b c ⇒ trans_ln a c
Proof
  metis_tac[trans_ln_def,RTC_RTC]
QED

(* Theorem trans_ln_NIL: *)
(*   ∀s sc. trans_ln (s,Nil) sc ⇒ sc = (s,Nil) *)
(* Proof *)
(*   metis_tac[trans_s_NIL,trans_ln_IMP_trans_s] *)
(* QED *)

Theorem trans_ln_merge_lemma:
  ∀sc sc' sc''.
  trans_ln (sc) (sc') ∧
  trans_ln (sc) (sc'') ⇒
  trans_ln (sc'') (sc') ∨ trans_ln (sc') (sc'')
Proof
  simp[trans_ln_def,GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[] >>
  pop_assum(strip_assume_tac o REWRITE_RULE[Once RTC_cases]) >>
  rveq >- (disj1_tac >> match_mp_tac RTC_TRANS >>
           rw[PULL_EXISTS] >> metis_tac[]) >>
  fs[] >> rveq >>
  first_x_assum drule >> strip_tac >>
  fs[]
QED

Theorem trans_ln_refl:
  trans_ln sc sc
Proof
  rw[trans_ln_def]
QED

Theorem trans_ln_merge:
  ∀c s τ l s' c' s'' c'' s''' c'''.
  trans (s,c) (τ,l) (s',c') ∧
  no_self_comunication c ∧ no_undefined_vars (s,c) ∧
  trans_ln (s,c) (s'',c'') ∧
  trans_ln (s',c') (s''',c''')
  ⇒ ∃s'''' c''''. trans_ln (s'',c'') (s'''',c'''') ∧ trans_ln (s''',c''') (s'''',c'''')
Proof
  Induct
  >- fs [Once trans_cases]
  \\ rw []
  \\  qpat_x_assum `trans _ _ _`
                   (ASSUME_TAC o SIMP_RULE std_ss [Once trans_cases])
  \\ rw [] >> rfs [] >> rw []
  \\ last_assum(mp_then Any mp_tac trans_ln_elim)
  \\ rw[chor_tl_def]
  >- (map_every qexists_tac [‘s''''’,‘c''''’]
      \\ simp [trans_ln_refl]
      \\ irule trans_ln_step
      \\ fs[chor_tl_def]
      \\ metis_tac [trans_rules])
  >- (qpat_x_assum ‘trans_ln (s',c) _’ (mp_then Any drule trans_ln_merge_lemma)
      \\ rw [] \\ metis_tac [trans_ln_refl])
  >- (map_every qexists_tac [‘s''''’,‘c''''’]
      \\ simp [trans_ln_refl]
      \\ irule trans_ln_step
      \\ fs[chor_tl_def]
      \\ metis_tac [trans_rules])
  >- (qpat_x_assum ‘trans_ln (s',c') _’ (mp_then Any drule trans_ln_merge_lemma)
      \\ rw [] \\ metis_tac [trans_ln_refl])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s',c)’ by(fs[no_undefined_vars_def,free_variables_def])
      \\ fs[]
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule_then (drule o REWRITE_RULE[FST]) lookup_fresh_after_trans
      \\ disch_then(qspec_then ‘s’ assume_tac)
      \\ drule trans_ln_elim
      \\ first_x_assum(qspecl_then [‘s'’,‘c’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ disch_then(qspecl_then [‘s''’,‘c1'’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ strip_tac
      \\ strip_tac \\ rveq
      >- (qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
          \\ conj_tac \\  match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ rfs[chor_tl_def] \\  metis_tac[trans_if_true])
      \\ rfs[chor_tl_def]
      \\ dxrule_then dxrule trans_ln_merge_lemma
      \\ rw[]
      >- (rename1 ‘_ ∧ trans_ln (sss,ccc) _’
          \\ qexists_tac ‘sss’ \\  qexists_tac ‘ccc’
          \\ simp[trans_ln_refl]
          \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ metis_tac[trans_ln_trans_ln,trans_if_true])
      \\ qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
      \\ simp[trans_ln_refl]
      \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
      \\ metis_tac[trans_ln_trans_ln,trans_if_true])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s',c)’ by(fs[no_undefined_vars_def,free_variables_def])
      \\ fs[]
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule_then (drule o REWRITE_RULE[FST]) lookup_fresh_after_trans
      \\ disch_then(qspec_then ‘s’ assume_tac)
      \\ first_x_assum drule
      \\ qpat_assum ‘trans_ln (s'',_) _’ (mp_then Any  mp_tac trans_ln_elim)
      \\ rw []
      >- (pop_assum (qspecl_then [‘s''’,‘c1'’] mp_tac) >> fs [trans_ln_refl]
          \\ rw [] >> asm_exists_tac >> fs []
          \\ irule trans_ln_step >> fs [chor_tl_def]
          \\ metis_tac [trans_if_true])
      \\ pop_assum irule \\ fs [chor_tl_def] \\ rfs [])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s',c')’ by(fs[no_undefined_vars_def,free_variables_def])
      \\ fs[]
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule_then (drule o REWRITE_RULE[FST]) lookup_fresh_after_trans
      \\ disch_then(qspec_then ‘s’ assume_tac)
      \\ drule trans_ln_elim
      \\ first_x_assum(qspecl_then [‘s'’,‘c'’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ disch_then(qspecl_then [‘s''’,‘c2'’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ strip_tac
      \\ strip_tac \\ rveq
      >- (qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
          \\ conj_tac \\  match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ rfs[chor_tl_def] \\  metis_tac[trans_if_false])
      \\ rfs[chor_tl_def]
      \\ dxrule_then dxrule trans_ln_merge_lemma
      \\ rw[]
      >- (rename1 ‘_ ∧ trans_ln (sss,ccc) _’
          \\ qexists_tac ‘sss’ \\  qexists_tac ‘ccc’
          \\ simp[trans_ln_refl]
          \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ metis_tac[trans_ln_trans_ln,trans_if_false])
      \\ qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
      \\ simp[trans_ln_refl]
      \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
      \\ metis_tac[trans_ln_trans_ln,trans_if_false])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s',c')’ by(fs[no_undefined_vars_def,free_variables_def])
      \\ fs[]
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule_then (drule o REWRITE_RULE[FST]) lookup_fresh_after_trans
      \\ disch_then(qspec_then ‘s’ assume_tac)
      \\ first_x_assum drule
      \\ qpat_assum ‘trans_ln (s'',_) _’ (mp_then Any  mp_tac trans_ln_elim)
      \\ rw []
      >- (pop_assum (qspecl_then [‘s''’,‘c2'’] mp_tac) >> fs [trans_ln_refl]
          \\ rw [] >> asm_exists_tac >> fs []
          \\ irule trans_ln_step >> fs [chor_tl_def]
          \\ metis_tac [trans_if_false])
      \\ pop_assum irule \\ fs [chor_tl_def] \\ rfs [])
  >- (rfs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP] \\ metis_tac[])
  >- (map_every qexists_tac [‘s''''’,‘c'''’]
      \\ simp [trans_ln_refl]
      \\ irule trans_ln_step
      \\ fs[chor_tl_def]
      \\ metis_tac [trans_rules])
  >- (qpat_x_assum ‘trans_ln (s' |+ _,c) _’ (mp_then Any drule trans_ln_merge_lemma)
      \\ rw [] \\ metis_tac [trans_ln_refl])
  >- (fs[no_self_comunication_def]
      \\ ‘∃d. FLOOKUP s' (s0,l0) = SOME d’
         by(fs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP])
      \\ ‘no_undefined_vars (s' |+ ((s,l),d),c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM]
           \\ metis_tac[])
      \\ drule lookup_fresh_after_trans \\  simp[]
      \\ disch_then(qspecl_then [‘l0’,‘s0’] mp_tac) \\  rw[]
      \\ drule semantics_add_irrelevant_state \\ simp[]
      \\ disch_then drule
      \\ disch_then(qspecl_then [‘s’,‘d’] assume_tac)
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule trans_ln_elim
      \\ first_x_assum(qspecl_then [‘s' |+ ((s,l),d)’,‘c’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ disch_then(qspecl_then [‘s'' |+ ((s,l),d)’,‘c''''’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ strip_tac
      \\ strip_tac \\ rveq
      >- (qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
          \\ conj_tac \\  match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ rfs[chor_tl_def] \\  metis_tac[trans_rules])
      \\ fs [chor_tl_def]
      \\ rfs [] \\ dxrule_all trans_ln_merge_lemma
      \\ rw []
      >- (qexists_tac ‘s''''’ \\  qexists_tac ‘c'''’ \\ fs [trans_ln_refl]
          \\ irule trans_ln_step \\ fs [chor_tl_def]
          \\ CONV_TAC EXISTS_AND_CONV
          \\ conj_tac >- metis_tac [trans_ln_trans_ln]
          \\ metis_tac [trans_rules])
      \\ qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
      \\ fs [chor_tl_def]
      \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
      \\ metis_tac[trans_ln_trans_ln,trans_rules])
  >- (fs[no_self_comunication_def]
      \\ ‘∃d. FLOOKUP s' (s0,l0) = SOME d’
         by(fs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP])
      \\ ‘no_undefined_vars (s' |+ ((s,l),d),c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM]
           \\ metis_tac[])
      \\ drule lookup_fresh_after_trans \\  simp[]
      \\ disch_then(qspecl_then [‘l0’,‘s0’] mp_tac) \\  rw[]
      \\ drule semantics_add_irrelevant_state \\ simp[]
      \\ disch_then drule
      \\ disch_then(qspecl_then [‘s’,‘d’] assume_tac)
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ fs [] \\ pop_assum drule \\ strip_tac
      \\ qpat_assum ‘trans_ln (s'',_) _’ (mp_then Any  mp_tac trans_ln_elim)
      \\ rw []
      >- (pop_assum (qspecl_then [‘s'' |+ ((s,l),d)’,‘c''''’] mp_tac) >> fs [trans_ln_refl]
          \\ rw [] >> asm_exists_tac >> fs []
          \\ irule trans_ln_step >> fs [chor_tl_def]
          \\ metis_tac [trans_rules])
      \\ first_x_assum irule \\ fs [chor_tl_def] \\ rfs [])
  >- (fs[no_self_comunication_def]
      \\ ‘∃d. FLOOKUP s' (s0,l0) = SOME d’
         by(fs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP])
      \\ ‘no_undefined_vars (s' |+ ((s,l),d),c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM]
           \\ metis_tac[])
      \\ drule lookup_unwritten_after_trans \\  simp[]
      \\ disch_then(qspecl_then [‘l0’,‘s0’] mp_tac) \\  rw[]
      \\ drule semantics_add_irrelevant_state \\ simp[]
      \\ disch_then drule
      \\ disch_then(qspecl_then [‘s’,‘d’] assume_tac)
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule trans_ln_elim
      \\ first_x_assum(qspecl_then [‘s' |+ ((s,l),d)’,‘c’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ disch_then(qspecl_then [‘s'' |+ ((s,l),d)’,‘c''''’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ strip_tac
      \\ strip_tac \\ rveq
      >- (qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
          \\ conj_tac \\  match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ fs [] \\ rfs[chor_tl_def] \\  metis_tac[trans_rules])
      \\ fs [chor_tl_def]
      \\ rfs [] \\ dxrule_all trans_ln_merge_lemma
      \\ rw []
      >- (qexists_tac ‘s''''’ \\  qexists_tac ‘c'''’ \\ fs [trans_ln_refl]
          \\ irule trans_ln_step \\ fs [chor_tl_def]
          \\ CONV_TAC EXISTS_AND_CONV
          \\ conj_tac >- metis_tac [trans_ln_trans_ln]
          \\ metis_tac [trans_rules])
      \\ qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
      \\ fs [chor_tl_def]
      \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
      \\ metis_tac[trans_ln_trans_ln,trans_rules])
  >- (fs[no_self_comunication_def]
      \\ ‘∃d. FLOOKUP s' (s0,l0) = SOME d’
         by(fs[no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP])
      \\ ‘no_undefined_vars (s' |+ ((s,l),d),c)’
        by(fs[no_undefined_vars_def,free_variables_def,SUBSET_DEF,DISJ_IMP_THM,FORALL_AND_THM]
           \\ metis_tac[])
      \\ drule lookup_unwritten_after_trans \\  simp[]
      \\ disch_then(qspecl_then [‘l0’,‘s0’] mp_tac) \\  rw[]
      \\ drule semantics_add_irrelevant_state \\ simp[]
      \\ disch_then drule
      \\ disch_then(qspecl_then [‘s’,‘d’] assume_tac)
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ fs [] \\ pop_assum drule \\ strip_tac
      \\ qpat_assum ‘trans_ln (s'',_) _’ (mp_then Any  mp_tac trans_ln_elim)
      \\ rw []
      >- (pop_assum (qspecl_then [‘s'' |+ ((s,l),d)’,‘c''''’] mp_tac) >> fs [trans_ln_refl]
          \\ rw [] >> asm_exists_tac >> fs []
          \\ irule trans_ln_step >> fs [chor_tl_def]
          \\ metis_tac [trans_rules])
      \\ first_x_assum irule \\ fs [chor_tl_def] \\ rfs [])
  >- (map_every qexists_tac [‘s''''’,‘c'''’]
      \\ fs [trans_ln_refl] \\ irule trans_ln_step
      \\ rw [chor_tl_def] \\ metis_tac [trans_rules])
  >- (qpat_x_assum ‘trans_ln (s' |+ _,c) _’ (mp_then Any drule trans_ln_merge_lemma)
      \\ rw [] \\ metis_tac [trans_ln_refl])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s' |+ ((s,l0),f (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,l0)) l))),c)’
        by(fs[no_undefined_vars_def,free_variables_def
              ,SUBSET_DEF,MEM_MAP,PULL_EXISTS
              ,DISJ_IMP_THM,FORALL_AND_THM]
           \\ metis_tac[])
      \\ drule_then assume_tac no_undefined_FLOOKUP_let
      \\ drule_then drule map_lookup_fresh_after_trans_tup
      \\ disch_then(qspec_then ‘l’ assume_tac)
      \\ drule semantics_add_irrelevant_state >> simp[] >> disch_then drule
      \\ disch_then(qspecl_then [‘s’,‘f (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,l0)) l))’] assume_tac)
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ qmatch_asmsub_abbrev_tac ‘((s,l0),d)’
      \\ drule trans_ln_elim
      \\ first_x_assum(qspecl_then [‘s' |+ ((s,l0),d)’,‘c’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ disch_then(qspecl_then [‘s'' |+ ((s,l0),d)’,‘c''''’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ UNABBREV_ALL_TAC
      \\ strip_tac
      \\ strip_tac \\ rveq
      >- (qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
          \\ conj_tac
          \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ rfs[chor_tl_def]
          >- metis_tac[trans_let]
          \\ qexists_tac ‘LLet s l0 f l’
          \\ qpat_x_assum ‘_ = _’ (assume_tac o GSYM)
          \\ simp []
          \\ irule trans_let
          \\ fs[EVERY_MEM,IS_SOME_EXISTS,MEM_MAP,PULL_EXISTS]
          \\ rw[] \\  res_tac
          \\ metis_tac[lookup_fresh_after_trans,FST])
      \\ fs [chor_tl_def]
      \\ rfs [] \\ dxrule_all trans_ln_merge_lemma
      \\ rw []
      >- (qexists_tac ‘s''''’ \\  qexists_tac ‘c'''’ \\ fs [trans_ln_refl]
          \\ irule trans_ln_step \\ fs [chor_tl_def]
          \\ CONV_TAC EXISTS_AND_CONV
          \\ conj_tac >- metis_tac [trans_ln_trans_ln]
          \\ metis_tac [trans_rules])
      \\ qexists_tac ‘s'''''’ \\  qexists_tac ‘c'''''’
      \\ fs [chor_tl_def]
      \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
      \\ metis_tac[trans_ln_trans_ln,trans_rules])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s' |+ ((s,l0),f (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,l0)) l))),c)’
        by(fs[no_undefined_vars_def,free_variables_def
              ,SUBSET_DEF,MEM_MAP,PULL_EXISTS
              ,DISJ_IMP_THM,FORALL_AND_THM]
           \\ metis_tac[])
      \\ drule_then assume_tac no_undefined_FLOOKUP_let
      \\ drule_then drule map_lookup_fresh_after_trans_tup
      \\ disch_then(qspec_then ‘l’ assume_tac)
      \\ drule semantics_add_irrelevant_state >> simp[] >> disch_then drule
      \\ disch_then(qspecl_then [‘s’,‘f (MAP (THE ∘ FLOOKUP s') (MAP (λv. (v,l0)) l))’] assume_tac)
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ fs [] \\ pop_assum drule \\ strip_tac
      \\ qpat_assum ‘trans_ln (s'',_) _’ (mp_then Any  mp_tac trans_ln_elim)
      \\ rw []
      >- (qmatch_asmsub_abbrev_tac ‘((s,l0),d)’
          \\ first_x_assum (qspecl_then [‘s'' |+ ((s,l0),d)’,‘c''''’] mp_tac) >> fs [trans_ln_refl]
          \\ UNABBREV_ALL_TAC
          \\ rw [] >> asm_exists_tac >> fs []
          \\ irule trans_ln_step >> fs [chor_tl_def]
          \\ qexists_tac ‘LLet s l0 f l’
          \\ qpat_x_assum ‘_ = _’ (assume_tac o GSYM)
          \\ simp []
          \\ irule trans_let
          \\ fs[EVERY_MEM,IS_SOME_EXISTS,MEM_MAP,PULL_EXISTS]
          \\ rw[] \\  res_tac
          \\ metis_tac[lookup_fresh_after_trans,FST])
      \\ first_x_assum irule \\ fs [chor_tl_def] \\ rfs [])
  >- (map_every qexists_tac [‘s'''’,‘c'''’]
      \\ fs [trans_ln_refl] \\ irule trans_ln_step
      \\ rw [chor_tl_def] \\ metis_tac [trans_rules])
  >- (qpat_x_assum ‘trans_ln (s,c) _’ (mp_then Any drule trans_ln_merge_lemma)
      \\ rw [] \\ metis_tac [trans_ln_refl])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s,c)’ by(fs[no_undefined_vars_def,free_variables_def])
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule trans_ln_elim
      \\ first_x_assum(qspecl_then [‘s’,‘c’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ disch_then(qspecl_then [‘s'’,‘c''''’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ strip_tac
      \\ strip_tac \\ rveq
      >- (qexists_tac ‘s''''’ \\  qexists_tac ‘c'''''’
          \\ conj_tac \\  match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ rfs[chor_tl_def] \\  metis_tac[trans_rules])
      \\ fs [chor_tl_def]
      \\ rfs [] \\ dxrule_all trans_ln_merge_lemma
      \\ rw []
      >- (qexists_tac ‘s'''’ \\  qexists_tac ‘c'''’ \\ fs [trans_ln_refl]
          \\ irule trans_ln_step \\ fs [chor_tl_def]
          \\ CONV_TAC EXISTS_AND_CONV
          \\ conj_tac >- metis_tac [trans_ln_trans_ln]
          \\ metis_tac [trans_rules])
      \\ qexists_tac ‘s''''’ \\  qexists_tac ‘c'''''’
      \\ fs [chor_tl_def]
      \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
      \\ metis_tac[trans_ln_trans_ln,trans_rules])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s,c)’ by(fs[no_undefined_vars_def,free_variables_def])
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ fs [] \\ pop_assum drule \\ strip_tac
      \\ qpat_assum ‘trans_ln (s',_) _’ (mp_then Any  mp_tac trans_ln_elim)
      \\ rw []
      >- (pop_assum (qspecl_then [‘s'’,‘c''''’] mp_tac) >> fs [trans_ln_refl]
          \\ rw [] >> asm_exists_tac >> fs []
          \\ irule trans_ln_step >> fs [chor_tl_def]
          \\ metis_tac [trans_rules])
      \\ first_x_assum irule \\ fs [chor_tl_def] \\ rfs [])
  >- (fs[no_self_comunication_def]
      \\ ‘no_undefined_vars (s,c)’ by(fs[no_undefined_vars_def,free_variables_def])
      \\ first_x_assum (drule_then drule) \\ strip_tac
      \\ drule trans_ln_elim
      \\ first_x_assum(qspecl_then [‘s’,‘c’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ disch_then(qspecl_then [‘s'’,‘c''''’] mp_tac)
      \\ simp[trans_ln_refl]
      \\ strip_tac
      \\ strip_tac \\ rveq
      >- (qexists_tac ‘s''''’ \\  qexists_tac ‘c'''''’
          \\ conj_tac \\  match_mp_tac trans_ln_step \\  rw[chor_tl_def]
          \\ rfs[chor_tl_def] \\  metis_tac[trans_rules])
      \\ fs [chor_tl_def]
      \\ rfs [] \\ dxrule_all trans_ln_merge_lemma
      \\ rw []
      >- (qexists_tac ‘s'''’ \\  qexists_tac ‘c'''’ \\ fs [trans_ln_refl]
          \\ irule trans_ln_step \\ fs [chor_tl_def]
          \\ CONV_TAC EXISTS_AND_CONV
          \\ conj_tac >- metis_tac [trans_ln_trans_ln]
          \\ metis_tac [trans_rules])
      \\ qexists_tac ‘s''''’ \\  qexists_tac ‘c'''''’
      \\ fs [chor_tl_def]
      \\ match_mp_tac trans_ln_step \\  rw[chor_tl_def]
      \\ metis_tac[trans_ln_trans_ln,trans_rules])
  \\ fs[no_self_comunication_def]
  \\ ‘no_undefined_vars (s,c)’ by(fs[no_undefined_vars_def,free_variables_def])
  \\ first_x_assum (drule_then drule) \\ strip_tac
  \\ fs [] \\ pop_assum drule \\ strip_tac
  \\ qpat_assum ‘trans_ln (s',_) _’ (mp_then Any  mp_tac trans_ln_elim)
  \\ rw []
  >- (pop_assum (qspecl_then [‘s'’,‘c''''’] mp_tac) >> fs [trans_ln_refl]
      \\ rw [] >> asm_exists_tac >> fs []
      \\ irule trans_ln_step >> fs [chor_tl_def]
      \\ metis_tac [trans_rules])
  \\ first_x_assum irule \\ fs [chor_tl_def] \\ rfs []
QED

Theorem trans_s_trans_s:
  trans_s a b ∧ trans_s b c ⇒ trans_s a c
Proof
  metis_tac[trans_s_def,RTC_RTC]
QED

Theorem trans_s_ln:
  ∀s c s' c'.
  no_self_comunication c ∧ no_undefined_vars (s,c) ∧
  trans_s (s,c) (s',c')
  ⇒ ∃s'' c''.
     trans_ln (s,c)   (s'',c'') ∧
     trans_s  (s',c') (s'',c'')
Proof
  simp[Once trans_s_def, RTC_eq_NRC,PULL_EXISTS] >>
  Induct_on ‘n’ >> rw[] >- (metis_tac[trans_ln_def,trans_s_def,RTC_REFL]) >>
  fs[NRC] >>
  rename1 ‘trans _ α sc'’ >>
  PairCases_on ‘sc'’ >>
  PairCases_on ‘α’ >>
  drule_all_then strip_assume_tac no_self_comunication_trans_pres >>
  drule_all_then strip_assume_tac no_undefined_vars_trans_pres >>
  drule_all_then strip_assume_tac trans_trans_ln >>
  first_x_assum(drule_all_then strip_assume_tac) >>
  drule_all_then strip_assume_tac trans_ln_merge >>
  qexists_tac ‘s''''’ >> qexists_tac ‘c''''’ >>
  metis_tac[trans_ln_IMP_trans_s,trans_s_trans_s,trans_ln_trans_ln]
QED

val _ = export_theory ()
