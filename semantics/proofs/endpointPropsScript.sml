open preamble choreoUtilsTheory endpointSemTheory endpointLangTheory;

val _ = new_theory "endpointProps"

 val _ = temp_delsimps ["NORMEQ_CONV"]

val trans_enqueue' = Q.store_thm("trans_enqueue'",
  `∀s d p1 p2 e q.
     p1 ≠ p2
     ⇒ trans (NEndpoint p2 (s with queue := q) e) (LReceive p1 d p2)
       (NEndpoint p2 (s with queue := SNOC (p1,d) q) e)`,
  rpt strip_tac
  >> `s with queue := SNOC (p1,d) q = (s with queue := q) with queue := SNOC (p1,d) ((s with queue := q).queue)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue
  >> simp[]);

val trans_enqueue_choice_r' = Q.store_thm("trans_enqueue_choice_r'",
  `∀s p1 p2 e q d.
     p1 ≠ p2 ⇒
     trans (NEndpoint p2 (s with queue := q) e) (LExtChoice p1 F p2)
       (NEndpoint p2 (s with queue := SNOC (p1,[0w]) q) e)`,
  rpt strip_tac
  >> `!d. s with queue := SNOC (p1,d) q = (s with queue := q) with queue := SNOC (p1,d) ((s with queue := q).queue)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue_choice_r
  >> simp[]);

val trans_enqueue_choice_l' = Q.store_thm("trans_enqueue_choice_l'",
  `∀s p1 p2 e q.
     p1 ≠ p2 ⇒
     trans (NEndpoint p2 (s with queue := q) e) (LExtChoice p1 T p2)
       (NEndpoint p2 (s with queue := SNOC (p1,[1w]) q) e)`,
  rpt strip_tac
  >> `!d. s with queue := SNOC (p1,d) q = (s with queue := q) with queue := SNOC (p1,d) ((s with queue := q).queue)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue_choice_l
  >> simp[]);

val trans_dequeue' = Q.store_thm("trans_dequeue'",
  `∀s v p1 p2 e q1 q2 d.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ⇒
     trans (NEndpoint p2 (s with queue := q1 ⧺ [(p1,d)] ⧺ q2) (Receive p1 v e)) LTau
       (NEndpoint p2
          <|bindings := s.bindings |+ (v,d);
            queue := q1 ⧺ q2|> e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s.bindings = (s with queue := a1).bindings` by simp[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac (trans_dequeue |> SIMP_RULE (srw_ss()) [])
  >> simp[]);

val trans_ext_choice_l' = Q.store_thm("trans_ext_choice_l'",
  `∀s p1 p2 e1 e2 q1 q2.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ⇒
     trans (NEndpoint p2 (s with queue := q1 ⧺ [(p1,[1w])] ⧺ q2) (ExtChoice p1 e1 e2)) LTau
       (NEndpoint p2 (s with queue := q1 ⧺ q2) e1)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s with queue := q1 ++ q2 = ((s with queue := a1) with queue := q1 ++ q2)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac (trans_ext_choice_l)
  >> simp[]);

val trans_ext_choice_r' = Q.store_thm("trans_ext_choice_r'",
  `∀s p1 p2 e1 e2 q1 d q2.
     p1 ≠ p2 ∧ d ≠ [1w] ∧
     EVERY (λ(p,_). p ≠ p1) q1 ⇒
     trans (NEndpoint p2 (s with queue := q1 ⧺ [(p1,d)] ⧺ q2) (ExtChoice p1 e1 e2)) LTau
           (NEndpoint p2 (s with queue := q1 ⧺ q2) e2)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s with queue := q1 ++ q2 = ((s with queue := a1) with queue := q1 ++ q2)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac (trans_ext_choice_r)
  >> simp[]);

val trans_let' = Q.store_thm("trans_let'",
  `∀s v p f vl e q.
         EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl) ⇒
         trans (NEndpoint p (s with queue:= q) (Let v f vl e)) LTau
           (NEndpoint p
              (<|bindings := s.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s.bindings) vl));
                 queue:= q
                 |>) e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `trans (NEndpoint _ s1 _) _ (NEndpoint _ s2 _)`
  >> `s2 = s1 with bindings := s1.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s1.bindings) vl))`
     by(unabbrev_all_tac >> simp[])
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac trans_let
  >> simp[]);

val trans_ext_choice_F_receive = Q.store_thm("trans_ext_choice_F_receive",
  `!e1 e2 p1 p2. trans e1 (LReceive p1 [0w] p2) e2 =
           trans e1 (LExtChoice p1 F p2) e2
  `,
  `!e1 alpha e2. trans e1 alpha e2 ==>
     !p1 p2. alpha = LReceive p1 [0w] p2 ==> trans e1 (LExtChoice p1 F p2) e2`
  by(ho_match_mp_tac trans_ind
     >> rpt strip_tac >> fs[] >> rveq >> fs[]
     >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[])
  >> `!e1 alpha e2. trans e1 alpha e2 ==>
       !p1 p2. alpha = LExtChoice p1 F p2 ==> trans e1 (LReceive p1 [0w] p2) e2`
    by(ho_match_mp_tac trans_ind
       >> rpt strip_tac >> fs[] >> rveq >> fs[]
       >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[])
  >> rw[EQ_IMP_THM]);

val trans_ext_choice_T_receive = Q.store_thm("trans_ext_choice_T_receive",
  `!e1 e2 p1 p2. trans e1 (LReceive p1 [1w] p2) e2 =
           trans e1 (LExtChoice p1 T p2) e2
  `,
  `!e1 alpha e2. trans e1 alpha e2 ==>
     !p1 p2. alpha = LReceive p1 [1w] p2 ==> trans e1 (LExtChoice p1 T p2) e2`
  by(ho_match_mp_tac trans_ind
     >> rpt strip_tac >> fs[] >> rveq >> fs[]
     >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[])
  >> `!e1 alpha e2. trans e1 alpha e2 ==>
       !p1 p2. alpha = LExtChoice p1 T p2 ==> trans e1 (LReceive p1 [1w] p2) e2`
    by(ho_match_mp_tac trans_ind
       >> rpt strip_tac >> fs[] >> rveq >> fs[]
       >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules) >> fs[])
  >> rw[EQ_IMP_THM]);

val trans_IMP_weak_trans = Q.store_thm("trans_IMP_weak_trans",
  `∀ p alpha q. trans p alpha q ==> weak_trans p alpha q`,
  rw[weak_trans_def,weak_tau_trans_def]
  >> metis_tac[RTC_REFL,RTC_SINGLE,reduction_def]);

val reduction_par_l = Q.store_thm("reduction_par_l",
  `∀p q r. reduction^* p q ==> reduction^* (NPar p r) (NPar q r)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_l]);

val reduction_par_r = Q.store_thm("reduction_par_r",
  `∀p q r. reduction^* p q ==> reduction^* (NPar r p) (NPar r q)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_r]);

val weak_trans_par_l = Q.store_thm("weak_trans_par_l",
  `∀p alpha q r. weak_trans p alpha q ==> weak_trans (NPar p r) alpha (NPar q r)`,
  rpt strip_tac >> fs[weak_trans_def] >> every_case_tac >> fs[weak_tau_trans_def]
  >> imp_res_tac reduction_par_l
  >> imp_res_tac trans_par_l
  >> rpt(first_x_assum (qspec_then `r` assume_tac))
  >> metis_tac[]);

val weak_trans_par_r = Q.store_thm("weak_trans_par_r",
  `∀p alpha q r. weak_trans p alpha q ==> weak_trans (NPar r p) alpha (NPar r q)`,
  rpt strip_tac >> fs[weak_trans_def] >> every_case_tac >> fs[weak_tau_trans_def]
  >> imp_res_tac reduction_par_r
  >> imp_res_tac trans_par_r
  >> rpt(first_x_assum (qspec_then `r` assume_tac))
  >> metis_tac[]);

val trans_nil_false = Q.store_thm("trans_nil_false",
  `∀conf alpha n. trans NNil alpha n = F`,
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[trans_cases]
  >> fs[]);

val reduction_nil = Q.store_thm("reduction_nil",
  `∀n. reduction^* NNil n ==> n = NNil`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = endpointLang$NNil`
  >> pop_assum (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> simp[]
  >> rpt(last_x_assum mp_tac)
  >> PURE_ONCE_REWRITE_TAC [AND_IMP_INTRO]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n`,`a1`]
  >> ho_match_mp_tac RTC_lifts_invariants
  >> simp[endpointSemTheory.reduction_def,trans_nil_false]);

val endpoints_def = Define `
   (endpoints endpointLang$NNil = [])
/\ (endpoints (NEndpoint p1 s e1) = [(p1,s,e1)])
/\ (endpoints (NPar n1 n2) = endpoints n1 ++ endpoints n2)`

val (junkcong_rules, junkcong_ind, junkcong_cases) = Hol_reln `
  (* Reflexive *)
  (∀fvs n:endpointLang$network. junkcong fvs n n)

  (* Symmetric *)
∧ (∀n1 n2 fvs.
    junkcong fvs n1 n2
    ⇒ junkcong fvs n2 n1)
  (* Transitive *)
∧ (∀n1 n2 n3 fvs.
     junkcong fvs n1 n2
     ∧ junkcong fvs n2 n3
     ⇒ junkcong fvs n1 n3)

  (* Add-junk *)
∧ (∀p s e v fvs d.
    v ∈ fvs ∧ ¬MEM v (free_var_names_endpoint e)
    ⇒ junkcong fvs (NEndpoint p s e) (NEndpoint p (s with bindings:= s.bindings |+ (v,d)) e))

  (* Par *)
∧ (∀n1 n2 n3 n4 fvs.
     junkcong fvs n1 n2
     ∧ junkcong fvs n3 n4
     ⇒ junkcong fvs (NPar n1 n3) (NPar n2 n4))`

val [junkcong_refl,junkcong_sym,junkcong_trans,junkcong_add_junk,junkcong_par]
    = zip ["junkcong_refl","junkcong_sym","junkcong_trans","junkcong_add_junk","junkcong_par"]
          (CONJUNCTS junkcong_rules) |> map save_thm;

val junkcong_strongind = fetch "-" "junkcong_strongind"

val junkcong_refl_IMP = Q.store_thm("junkcong_refl_IMP",
  `∀fvs n n'. n = n' ==> junkcong fvs n n'`,
  simp[junkcong_refl]);

val junkcong_add_junk' = Q.store_thm("junkcong_add_junk'",
 `∀p s b e v fvs d.
    v ∈ fvs ∧ ¬MEM v (free_var_names_endpoint e)
    ⇒ junkcong fvs (NEndpoint p (s with bindings := b) e) (NEndpoint p (s with bindings:= b |+ (v,d)) e)`,
 rpt strip_tac
 >> `s with bindings := b |+ (v,d) =
     (s with bindings := b) with bindings := (s with bindings := b).bindings |+ (v,d)`
      by simp[]
 >> pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm])
 >> match_mp_tac junkcong_add_junk >> simp[]);

val junkcong_add_junk'' = Q.store_thm("junkcong_add_junk''",
 `∀p b q e v fvs d.
    v ∈ fvs ∧ ¬MEM v (free_var_names_endpoint e)
    ⇒ junkcong fvs (NEndpoint p <|bindings := b; queue := q|> e)
                    (NEndpoint p <|bindings := b |+ (v,d); queue := q|> e)`,
 rpt strip_tac
 >> qmatch_goalsub_abbrev_tac `junkcong _ (NEndpoint _ a1 _) (NEndpoint _ a2 _)`
 >> `a2 = a1 with bindings := a1.bindings |+ (v,d)`
     by(unabbrev_all_tac >> simp[])
 >> rveq
 >> match_mp_tac junkcong_add_junk >> simp[]);

val junkcong_add_junk''' = Q.store_thm("junkcong_add_junk'''",
  `∀p s q e v fvs d.
     v ∈ fvs ∧ ¬MEM v (free_var_names_endpoint e) ⇒
     junkcong fvs (NEndpoint p (s with queue := q) e)
     (NEndpoint p (s with <|bindings := s.bindings |+ (v,d); queue := q|>) e)`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = s with queue := q`
  >> `s.bindings = a1.bindings` by(unabbrev_all_tac >> simp[])
  >> fs[junkcong_add_junk]);

val junkcong_remove_junk = Q.store_thm("junkcong_remove_junk",
  `(∀p s e v fvs.
    v ∈ fvs ∧ ¬MEM v (free_var_names_endpoint e)
    ⇒ junkcong fvs (NEndpoint p s e) (NEndpoint p (s with bindings:= s.bindings \\ v) e))`,
  rpt strip_tac
  >> Cases_on `v ∈ FDOM s.bindings`
  >- (fs[FDOM_FLOOKUP] >> rename1 `FLOOKUP _ _ = SOME d`
      >> drule junkcong_add_junk >> disch_then drule
      >> disch_then (qspecl_then [`p`,`s with bindings := s.bindings \\ v`,`d`] assume_tac)
      >> fs[GSYM FUPDATE_PURGE]
      >> `s.bindings |+ (v,d) = s.bindings`
           by(match_mp_tac FUPDATE_ELIM >> fs[flookup_thm])
      >> `s with bindings := s.bindings = s` by fs[endpointLangTheory.state_component_equality]
      >> fs[FUPDATE_ELIM] >> match_mp_tac junkcong_sym >> first_x_assum ACCEPT_TAC)
  >- (fs[DOMSUB_NOT_IN_DOM]
      >> match_mp_tac junkcong_refl_IMP >> simp[endpointLangTheory.state_component_equality]));

val junkcong_sym_eq = Q.store_thm("junkcong_sym_eq",
`∀fvs p q. junkcong fvs p q = junkcong fvs q p`,metis_tac[junkcong_sym]);

Theorem MEM_free_var_names_endpoint_dsubst:
  MEM x (free_var_names_endpoint(dsubst e dn e')) ⇒
  MEM x (free_var_names_endpoint e') ∨ MEM x (free_var_names_endpoint e)
Proof
  Induct_on ‘e’ >> rw[free_var_names_endpoint_def,dsubst_def] >>
  res_tac >> fs[] >>
  fs[MEM_FILTER]
QED

Theorem MEM_var_names_endpoint_dsubst:
  MEM x (var_names_endpoint(dsubst e dn e')) ⇒
  MEM x (var_names_endpoint e') ∨ MEM x (var_names_endpoint e)
Proof
  Induct_on ‘e’ >> rw[var_names_endpoint_def,dsubst_def] >>
  res_tac >> fs[]
QED

val junkcong_trans_eq = Q.store_thm("junkcong_trans_eq",
  `∀fvs p1 q1.
     junkcong fvs p1 q1
     ⇒ ∀ alpha p2 q2.
            ((trans p1 alpha p2 ⇒ (∃q2. trans q1 alpha q2 ∧ junkcong fvs p2 q2))
         ∧ (trans q1 alpha q2 ⇒ (∃p2. trans p1 alpha p2 ∧ junkcong fvs p2 q2)))`,
  ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- (* junkcong_add_junk *)
     (‘∃p1. p1 = NEndpoint p s e’ by simp[]
      >> pop_assum(fn thm => SUBST_ALL_TAC(GSYM thm) >> mp_tac thm)
      >> qhdtm_x_assum ‘trans’ (fn thm => rpt(pop_assum mp_tac) >> assume_tac thm)
      >> MAP_EVERY qid_spec_tac [‘fvs’,‘e’,‘p’,‘s’]
      >> pop_assum mp_tac
      >> MAP_EVERY qid_spec_tac [‘p2’,‘alpha’,‘p1’]
      >> ho_match_mp_tac trans_ind
      >> rw[] >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with bindings := a2.bindings |+ (v,d)) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS endpointSemTheory.trans_rules)
                 >> fs[FLOOKUP_UPDATE,free_var_names_endpoint_def])
             >- (`¬MEM v (free_var_names_endpoint a3)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> fs[free_var_names_endpoint_def] >> metis_tac[junkcong_rules]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with queue := a3) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with <|queue := a3; bindings := a2.bindings |+ (v,d)|>) a4`
             >> conj_tac
             >- (PURE_ONCE_REWRITE_TAC [endpointLangTheory.state_fupdcanon]
                 >> qmatch_goalsub_abbrev_tac `trans (NEndpoint _ a5 _)`
                 >> `a2 with <|bindings := a2.bindings |+ (v,d); queue := a3|>
                     = a5 with queue := a3` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> qunabbrev_tac `a3`
                 >> `a2.queue = a5.queue` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> simp[])
             >- (imp_res_tac junkcong_add_junk
                 >> pop_assum(qspec_then `a2 with queue := a3` assume_tac)
                 >> fs[]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1
                                                                <|bindings := a2;
                                                                  queue := a3|>
                                                                a4)`
             >> qexists_tac `NEndpoint a1 <|bindings := if v = v' then a2
                                                        else a2 |+ (v,d); queue := a3|> a4`
             >> conj_tac
             >- (IF_CASES_TAC
                 >> unabbrev_all_tac
                 >> `s.queue = (s with bindings := s.bindings |+ (v,d)).queue` by simp[]
                 >> pop_assum(fn thm => FULL_SIMP_TAC bool_ss [Once thm])
                 >> imp_res_tac trans_dequeue
                 >> first_x_assum(qspec_then `v'` assume_tac)
                 >> rveq
                 >> fs[Once FUPDATE_COMMUTES])
             >- (IF_CASES_TAC
                 >- metis_tac[junkcong_rules]
                 >> `¬MEM v (free_var_names_endpoint a4)`
                     by(unabbrev_all_tac >> fs[free_var_names_endpoint_def,MEM_FILTER])
                 >> metis_tac[junkcong_add_junk'']))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with queue := a3) a4)`
             >> qexists_tac `NEndpoint a1 (<|queue := a3;
                                             bindings := a2.bindings |+ (v,d)|>) a4`
             >> conj_tac
             >- (PURE_ONCE_REWRITE_TAC [endpointLangTheory.state_fupdcanon]
                 >> qmatch_goalsub_abbrev_tac `trans (NEndpoint _ a5 _)`
                 >> `<|bindings := a2.bindings |+ (v,d); queue := a3|>
                     = a5 with queue := a3` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> qunabbrev_tac `a4`
                 >> qunabbrev_tac `a3`
                 >> `a2.queue = a5.queue` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> unabbrev_all_tac >> simp[])
             >- (`¬MEM v (free_var_names_endpoint a4)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> imp_res_tac junkcong_add_junk
                 >> rpt(first_x_assum(qspec_then `a2 with queue := a3` assume_tac ))
                 >> fs[]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with bindings := a3) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with bindings := if v = v' then a3
                                                               else a3|+ (v,d)) a4`
             >> conj_tac
             >- (IF_CASES_TAC
                 >> unabbrev_all_tac >> fs[free_var_names_endpoint_def,MEM_FILTER]
                 >> `EVERY IS_SOME (MAP (FLOOKUP ((s with bindings := s.bindings |+ (v,d)).bindings)) vl)`
                     by(fs[EVERY_MAP,FLOOKUP_UPDATE,EVERY_MEM] >> rw[])
                 >> drule trans_let >> fs[] >> disch_then(qspecl_then [`v'`] assume_tac)
                 >> `MAP (THE ∘ FLOOKUP (s.bindings |+ (v,d))) vl
                     = MAP (THE ∘ FLOOKUP s.bindings) vl`
                     by(rw[MAP_EQ_f,FLOOKUP_UPDATE] >> rw[] >> fs[])
                 >> rfs[] >> fs[Once FUPDATE_COMMUTES])
             >- (IF_CASES_TAC
                 >- metis_tac[junkcong_rules]
                 >- (match_mp_tac junkcong_add_junk' >> fs[free_var_names_endpoint_def,MEM_FILTER])))
      >> TRY(rename1 ‘dsubst e dn (Fix dn e)’
             >> qexists_tac ‘NEndpoint p (s with bindings := s.bindings |+ (v,d)) (dsubst e dn (Fix dn e))’
             >> conj_tac >- metis_tac[trans_fix]
             >> match_mp_tac junkcong_add_junk
             >> simp[]
             >> spose_not_then strip_assume_tac >> imp_res_tac MEM_free_var_names_endpoint_dsubst
             >> fs[free_var_names_endpoint_def])
     )
  >- (* junkcong_add_junk, symmetric case *)
     (PURE_ONCE_REWRITE_TAC [junkcong_sym_eq]
      >> ‘∃q1. q1 = NEndpoint p (s with bindings := s.bindings |+ (v,d)) e’ by simp[]
      >> pop_assum(fn thm => SUBST_ALL_TAC(GSYM thm) >> mp_tac thm)
      >> qhdtm_x_assum ‘trans’ (fn thm => rpt(pop_assum mp_tac) >> assume_tac thm)
      >> MAP_EVERY qid_spec_tac [‘fvs’,‘e’,‘p’,‘s’]
      >> pop_assum mp_tac
      >> MAP_EVERY qid_spec_tac [‘q2’,‘alpha’,‘q1’]
      >> ho_match_mp_tac trans_ind
      >> rw[] >> fs[] >> rveq
      >> rename1 ‘NEndpoint _ s’
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with bindings := _) a3)`
             >> qexists_tac `NEndpoint a1 a2 a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS endpointSemTheory.trans_rules)
                 >> fs[FLOOKUP_UPDATE,free_var_names_endpoint_def] >> rfs[])
             >- (`¬MEM v (free_var_names_endpoint a3)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> fs[free_var_names_endpoint_def] >> metis_tac[junkcong_rules]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs
                                                (NEndpoint a1
                                                           <|bindings := a2 |+ _ |+ (a3,a4);
                                                             queue := a5|> a6)`
             >> qexists_tac `NEndpoint a1 (s with <|queue := a5; bindings := a2 |+ (a3,a4)|>) a6`
             >> conj_tac
             >- (unabbrev_all_tac >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> simp[])
             >- (Cases_on `v = a3` >> fs[Once FUPDATE_COMMUTES]
                 >> fs[free_var_names_endpoint_def,MEM_FILTER]
                 >> metis_tac[junkcong_rules,junkcong_add_junk']))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs
                                                (NEndpoint a1
                                                           <|bindings := a2 |+ (v,d);
                                                             queue := a3|> a4)`
             >> qexists_tac `NEndpoint a1 (s with queue := a3) a4`
             >> conj_tac
             >- (PURE_ONCE_REWRITE_TAC [endpointLangTheory.state_fupdcanon]
                 >> unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> simp[])
             >- (`¬MEM v (free_var_names_endpoint a4)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> imp_res_tac junkcong_add_junk
                 >> rpt(first_x_assum(qspec_then `s with queue := a3` assume_tac))
                 >> fs[] >> rw[Once junkcong_sym_eq] >> unabbrev_all_tac >> fs[]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs
                                                 (NEndpoint a1
                                                            (s with bindings := a2 |+ _ |+ (a3,a4))
                                                            a5)`
             >> qexists_tac `NEndpoint a1 (s with bindings := a2 |+ (a3,a4)) a5`
             >> conj_tac
             >- (unabbrev_all_tac >> fs[free_var_names_endpoint_def,MEM_FILTER]
                 >> `MAP (THE ∘ FLOOKUP (s.bindings |+ (v,d))) vl
                     = MAP (THE ∘ FLOOKUP s.bindings) vl`
                      by(rw[MAP_EQ_f,FLOOKUP_UPDATE] >> rw[] >> fs[])
                 >> fs[] >> match_mp_tac trans_let >> fs[EVERY_MAP,EVERY_MEM] >> rw[]
                 >> first_x_assum drule >> strip_tac >> fs[IS_SOME_EXISTS,FLOOKUP_UPDATE]
                 >> every_case_tac >> fs[])
             >- (Cases_on `a3 = v` >> fs[Once FUPDATE_COMMUTES]
                 >> fs[free_var_names_endpoint_def,MEM_FILTER]
                 >> metis_tac[junkcong_rules,junkcong_add_junk']))
      >> TRY(rename1 ‘dsubst e dn (Fix dn e)’
             >> qexists_tac ‘NEndpoint p s (dsubst e dn (Fix dn e))’
             >> conj_tac >- metis_tac[trans_fix]
             >> match_mp_tac junkcong_sym
             >> match_mp_tac junkcong_add_junk
             >> simp[]
             >> spose_not_then strip_assume_tac >> imp_res_tac MEM_free_var_names_endpoint_dsubst
             >> fs[free_var_names_endpoint_def]))
  >- (* par-l *)
     (qpat_x_assum `trans (NPar _ _) _ _` (assume_tac
                                    o REWRITE_RULE [Once endpointSemTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_com_choice_l
      >> imp_res_tac trans_com_choice_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[junkcong_rules])
  >- (* par-r *)
     (qpat_x_assum `trans (NPar _ _) _ _` (assume_tac
                                    o REWRITE_RULE [Once endpointSemTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_com_choice_l
      >> imp_res_tac trans_com_choice_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[junkcong_rules]));

val junkcong_reduction_eq = Q.store_thm("junkcong_reduction_eq",
  `∀fvs p1 q1.
     junkcong fvs p1 q1
     ⇒ ∀ p2 q2.
         ((reduction^* p1 p2 ⇒ (∃q2. reduction^* q1 q2 ∧ junkcong fvs p2 q2))
         ∧ (reduction^* q1 q2 ⇒ (∃p2. reduction^* p1 p2 ∧ junkcong fvs p2 q2)))`,
  rw []
  >- (last_x_assum mp_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`q2`,`q1`,`fvs`]
      \\ first_x_assum mp_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`p1`]
      \\ ho_match_mp_tac RTC_ind \\ rw []
      >- (qexists_tac ‘q1’ \\ fs [junkcong_rules])
      \\ fs [reduction_def]
      \\ drule_then (qspecl_then [‘LTau’,‘p1'’,‘q1'’] assume_tac) junkcong_trans_eq
      \\ rfs [] \\ first_x_assum drule \\ rw [] \\ qexists_tac ‘q2'’ \\ rw []
      \\ rw [reduction_def] \\ irule RTC_TRANS \\ qexists_tac ‘q2’ \\ rw []
      \\ rw [reduction_def])
  \\ last_x_assum mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`p1`,`fvs`]
  \\ first_x_assum mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`q2`,`q1`]
  \\ ho_match_mp_tac RTC_ind \\ rw []
  >- (qexists_tac ‘p1’ \\ fs [junkcong_rules])
  \\ fs [reduction_def]
  \\ drule_then (qspecl_then [‘LTau’,‘p1'’,‘q1'’] assume_tac) junkcong_trans_eq
  \\ rfs [] \\ first_x_assum drule \\ rw [] \\ qexists_tac ‘p2'’ \\ rw []
  \\ rw [reduction_def] \\ irule RTC_TRANS \\ qexists_tac ‘p2’ \\ rw []
  \\ rw [reduction_def]
);

val junkcong_has_fv_eq = Q.store_thm("junkcong_has_fv_eq",
  `!fv e l s e2. junkcong {fv} (NEndpoint l s e) e2
   /\ MEM fv (free_var_names_endpoint e)
   ==> NEndpoint l s e = e2`,
  `!fvs e1 e2. junkcong fvs e1 e2
   ==> (!fv e l s. e1 = NEndpoint l s e /\ fvs = {fv} /\ MEM fv (free_var_names_endpoint e)
                        ==> NEndpoint l s e = e2) /\
       (!fv e l s. e2 = NEndpoint l s e /\ fvs = {fv} /\ MEM fv (free_var_names_endpoint e)
                        ==> e1 = NEndpoint l s e)
  ` suffices_by metis_tac[]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac
  >> fs[] >> rveq >> fs[]);

val junkcong_nil_rel_nil = Q.store_thm("junkcong_nil_rel_nil",
  `!fvs n2.
   junkcong fvs NNil n2 ==> n2 = NNil`,
  `!fvs n1 n2.
    junkcong fvs n1 n2
    ==> (n1 = NNil <=> n2 = NNil)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac >> fs[]);

val junkcong_par_rel_par = Q.store_thm("junkcong_par_rel_par",
  `!fvs n1 n2 n3.
   junkcong fvs (NPar n1 n2) n3 ==> ?n4 n5. n3 = NPar n4 n5 /\ junkcong fvs n1 n4 /\ junkcong fvs n2 n5`,
  `!fvs n1 n2.
    junkcong fvs n1 n2
    ==> (!n3 n4. n1 = NPar n3 n4 ==> ?n5 n6. n2 = NPar n5 n6 /\ junkcong fvs n3 n5 /\ junkcong fvs n4 n6)
        /\ (!n3 n4. n2 = NPar n3 n4 ==> ?n5 n6. n1 = NPar n5 n6 /\ junkcong fvs n5 n3 /\ junkcong fvs n6 n4)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac >> fs[junkcong_refl,junkcong_sym]
  >> rfs[] >> fs[] >> metis_tac[junkcong_trans]);

val junkcong_endpoint_rel_endpoint = Q.store_thm("junkcong_endpoint_rel_endpoint",
  `!fvs p1 s1 e1 n2.
   junkcong fvs (NEndpoint p1 s1 e1) n2 ==> ?s2. n2 = NEndpoint p1 s2 e1`,
  `!fvs n1 n2.
    junkcong fvs n1 n2
    ==> (!p1 s1 e1. n1 = NEndpoint p1 s1 e1 ==> ?s2. n2 = NEndpoint p1 s2 e1)
        /\ !p2 s2 e2. n2 = NEndpoint p2 s2 e2 ==> ?s1. n1 = NEndpoint p2 s1 e2`
    suffices_by metis_tac[]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac >> fs[]);

val junkcong_endpoint_queue_eq = Q.store_thm("junkcong_endpoint_queue_eq",
  `!fvs p1 s1 s2 e1 .
   junkcong fvs (NEndpoint p1 s1 e1) (NEndpoint p1 s2 e1) ==> s1.queue = s2.queue`,
  `!fvs n1 n2.
    junkcong fvs n1 n2
    ==> (!p1 s1 s2 e1. n1 = NEndpoint p1 s1 e1 /\ n2 = NEndpoint p1 s2 e1
          ==> s1.queue = s2.queue)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> simp[] >> metis_tac [junkcong_rules,junkcong_endpoint_rel_endpoint]);

val junkcong_endpoints = Q.store_thm("junkcong_endpoints",
  `!fvs n1 n2. junkcong fvs n1 n2 ==> MAP FST (endpoints n1) = MAP FST (endpoints n2)`,
  ho_match_mp_tac junkcong_ind
  >> rpt strip_tac >> fs[endpoints_def]);

val junkcong_trans_pres = Q.store_thm("junkcong_trans_pres",
  `∀p1 q1 fv alpha p2.
     junkcong fv p1 q1 ∧ trans p1 alpha p2
     ⇒ ∃q2. trans q1 alpha q2 ∧ junkcong fv p2 q2`,
  metis_tac[junkcong_trans_eq])

val junkcong_reduction_pres = Q.store_thm("junkcong_reduction_pres",
  `∀p1 q1 fv alpha p2.
     junkcong fv p1 q1 ∧ reduction^* p1 p2
     ⇒ ∃q2. reduction^* q1 q2 ∧ junkcong fv p2 q2`,
  metis_tac[junkcong_reduction_eq])

val (qcong_rules, qcong_ind, qcong_cases) = Hol_reln `
  (* Reflexive *)
  (∀n. qcong n n)

  (* Symmetric *)
∧ (∀n1 n2.
    qcong n1 n2
    ⇒ qcong n2 n1)
  (* Transitive *)
∧ (∀n1 n2 n3.
     qcong n1 n2
     ∧ qcong n2 n3
     ⇒ qcong n1 n3)

  (* Queue-Reorder *)
∧ (∀p s e p1 d1 p2 d2 q1 q2.
    s.queue = q1 ++ [(p1,d1);(p2,d2)] ++ q2
    ∧ p1 ≠ p2
    ⇒ qcong (NEndpoint p s e) (NEndpoint p (s with queue:= q1 ++ [(p2,d2);(p1,d1)] ++ q2) e))

  (* Par *)
∧ (∀n1 n2 n3 n4.
     qcong n1 n2
     ∧ qcong n3 n4
     ⇒ qcong (NPar n1 n3) (NPar n2 n4))`

val [qcong_refl,qcong_sym,qcong_trans,qcong_queue_reorder,qcong_par]
    = zip ["qcong_refl","qcong_sym","qcong_trans","qcong_queue_reorder","qcong_par"]
          (CONJUNCTS qcong_rules) |> map save_thm;

val qcong_strongind = fetch "-" "qcong_strongind"

val (qrel_rules, qrel_ind, qrel_cases) = Hol_reln `
  (* Reflexive *)
  (∀q. qrel q q)

  (* Symmetric *)
∧ (∀q1 q2.
    qrel q1 q2
    ⇒ qrel q2 q1)
  (* Transitive *)
∧ (∀q1 q2 q3.
     qrel q1 q2
     ∧ qrel q2 q3
     ⇒ qrel q1 q3)

  (* Queue-Reorder *)
∧ (∀p1 d1 p2 d2 q1 q2.
    p1 ≠ p2
    ⇒ qrel (q1 ++ [(p1,d1);(p2,d2)] ++ q2) (q1 ++ [(p2,d2);(p1,d1)] ++ q2))`

val qrel_strongind = fetch "-" "qrel_strongind"

val [qrel_refl,qrel_sym,qrel_trans,qrel_queue_reorder]
    = zip ["qrel_refl","qrel_sym","qrel_trans","qrel_queue_reorder"]
          (CONJUNCTS qrel_rules) |> map save_thm;

val qcong_queue_reorder' = Q.store_thm("qcong_queue_reorder'",
  `∀p s e p1 d1 p2 d2 q1 q2.
     p1 ≠ p2
     ⇒ qcong (NEndpoint p (s with queue:=q1 ++ [(p1,d1);(p2,d2)] ++ q2) e)
              (NEndpoint p (s with queue:= q1 ++ [(p2,d2);(p1,d1)] ++ q2) e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `qcong (NEndpoint _ (_ with queue := a1) _) (NEndpoint _ (_ with queue := a2) _)`
  >> `s with queue := a2 = (s with queue := a1) with queue := a2` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac qcong_queue_reorder
  >> simp[]);

val qrel_IMP_qcong = Q.store_thm("qrel_IMP_qcong",
  `!q1 q2 p s e.
    qrel q1 q2
    ==> qcong (NEndpoint p (s with queue := q1) e) (NEndpoint p (s with queue := q2) e)`,
  simp[GSYM PULL_FORALL]
  >> ho_match_mp_tac qrel_strongind
  >> metis_tac[qcong_rules,qcong_queue_reorder'])

val qrel_cons = Q.store_thm("qrel_cons",
  `!q1 q2 qe. qrel q1 q2 ==> qrel (qe::q1) (qe::q2)`,
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >> `!a b. qe::(a ++ b) = qe::a ++ b` by simp[]
  >> ASM_SIMP_TAC pure_ss [] >> pop_assum kall_tac
  >> metis_tac[qrel_rules]);

val qrel_snoc = Q.store_thm("qrel_snoc",
  `!q1 q2 qe. qrel q1 q2 ==> qrel (SNOC qe q1) (SNOC qe q2)`,
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >> simp[SNOC_APPEND]
  >> metis_tac[qrel_rules,APPEND_ASSOC]);

val qrel_append_l = Q.store_thm("qrel_append_l",
  `!q1 q2 q3. qrel q2 q3 ==> qrel (q1++q2) (q1++q3)`,
  Induct >> simp[] >> metis_tac[qrel_cons]);

val qrel_append_r = Q.store_thm("qrel_append_r",
  `!q3 q1 q2. qrel q1 q2 ==> qrel (q1++q3) (q2++q3)`,
  ho_match_mp_tac SNOC_INDUCT >> rpt strip_tac >> simp[APPEND_SNOC] >> metis_tac[qrel_snoc]);

val qrel_append = Q.store_thm("qrel_append",
  `!q1 q2 q3 q4. qrel q1 q2 /\ qrel q3 q4 ==> qrel (q1++q3) (q2++q4)`,
  metis_tac[qrel_rules,qrel_append_l,qrel_append_r]);

val qrel_LENGTH = Q.store_thm("qrel_LENGTH",
  `!q1 q2. qrel q1 q2 ==> LENGTH q1 = LENGTH q2`,
  ho_match_mp_tac qrel_ind >> rw[]);

val qrel_PERM = Q.store_thm("qrel_PERM",
  `!q1 q2. qrel q1 q2 ==> PERM q1 q2`,
  ho_match_mp_tac qrel_strongind
  >> rpt strip_tac
  >> fs[PERM_SYM]
  >- metis_tac[PERM_TRANS]
  >- CONV_TAC permLib.PERM_ELIM_DUPLICATES_CONV);

val qrel_cons_IMP_lemma = Q.prove(
  `!q1l q1r q2 qe. qrel (q1l ++ [qe] ++ q1r) q2 /\ EVERY (λ(p,_). p ≠ FST qe) q1l ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l ++ q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2l`,
  `!q1 q2. qrel q1 q2 ==> ((!q1l q1r qe. q1 = q1l ++ [qe] ++ q1r /\ EVERY (λ(p,_). p ≠ FST qe) q1l ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2l)
                           /\ (!q2l q2r qe. q2 = q2l ++ [qe] ++ q2r /\ EVERY (λ(p,_). p ≠ FST qe) q2l ==> ?q1l q1r. q1 = q1l ++ [qe] ++ q1r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q1l))`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac >> rveq
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_sym]
  >- metis_tac[qrel_sym]
  >- (last_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l'`,`q2r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (first_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l'`,`q1r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q1l` >> rw[]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p2,d2)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p2,d2); (p1,d1)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC]))
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q2l` >> rw[]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p1,d1)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p1,d1); (p2,d2)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])));

val qrel_snoc_IMP_lemma = Q.prove(
  `!q1l q1r q2 qe. qrel (q1l ++ [qe] ++ q1r) q2 /\ EVERY (λ(p,_). p ≠ FST qe) q1r ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l ++ q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2r`,
  `!q1 q2. qrel q1 q2 ==> ((!q1l q1r qe. q1 = q1l ++ [qe] ++ q1r /\ EVERY (λ(p,_). p ≠ FST qe) q1r ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2r)
                           /\ (!q2l q2r qe. q2 = q2l ++ [qe] ++ q2r /\ EVERY (λ(p,_). p ≠ FST qe) q2r ==> ?q1l q1r. q1 = q1l ++ [qe] ++ q1r /\ qrel (q1l++q1r) (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q1r))`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac >> rveq
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_refl]
  >- metis_tac[qrel_sym]
  >- metis_tac[qrel_sym]
  >- (last_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> last_x_assum (qspecl_then [`q2l'`,`q2r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (first_x_assum (qspecl_then [`q2l`,`q2r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l`,`q1r`,`qe`] assume_tac)
      >> rfs[] >> rveq
      >> first_x_assum (qspecl_then [`q1l'`,`q1r'`,`qe`] assume_tac) (* TODO: generated names *)
      >> rfs[] >> rveq
      >> metis_tac[qrel_trans])
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q1l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC,EVERY_APPEND])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p2,d2)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p2,d2); (p1,d1)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC]))
  >- (qpat_x_assum `_ = _` (assume_tac o REWRITE_RULE [APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)])
      >> fs[] >> rveq
      >- (qexists_tac `q2l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC,EVERY_APPEND])
      >- (rename1 `[_;_] = a1 ++ _ ++ _`
          >> Cases_on `a1`
          >- (fs[] >> rveq >> qexists_tac `q1++[(p1,d1)]` >> rw[qrel_refl])
          >> fs[] >> rveq
          >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq
          >> qexists_tac `q1` >> rw[]
          >> qmatch_goalsub_abbrev_tac `qrel a1 a2`
          >> `a1 = a2` suffices_by rw[qrel_refl]
          >> unabbrev_all_tac
          >> rw[])
      >- (qexists_tac `q1 ++ [(p1,d1); (p2,d2)] ++ l` >> rw[] >> fs[EVERY_APPEND]
          >> metis_tac[qrel_queue_reorder,APPEND_ASSOC])));

val qrel_cons_IMP = Q.prove(
  `!q1 q2 qe. qrel (qe::q1) q2 ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel q1 (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2l`,
  rpt gen_tac
  >> `qe::q1 = [] ++ [qe] ++ q1` by rw[]
  >> pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> rpt strip_tac
  >> dxrule qrel_cons_IMP_lemma >> rw[]);

val qrel_snoc_IMP = Q.prove(
  `!q1 q2 qe. qrel (SNOC qe q1) q2 ==> ?q2l q2r. q2 = q2l ++ [qe] ++ q2r /\ qrel q1 (q2l++q2r) /\ EVERY (λ(p,_). p ≠ FST qe) q2r`,
  rpt gen_tac
  >> `SNOC qe q1 = q1 ++ [qe] ++ []` by rw[SNOC_APPEND]
  >> pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> rpt strip_tac
  >> dxrule qrel_snoc_IMP_lemma >> rw[]);

val qrel_consE = Q.store_thm("qrel_consE",
  `!q1 q2 qe. qrel (qe::q1) (qe::q2) ==> qrel q1 q2`,
  `!qq1 qq2. qrel qq1 qq2 ==> (!q1 q2 qe. qq1 = (qe::q1) /\ qq2 = (qe::q2) ==> qrel q1 q2)`
    suffices_by metis_tac[qrel_refl]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >> fs[] >> rveq
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- (imp_res_tac qrel_LENGTH
      >> qpat_x_assum `qrel _ (_::_)` (assume_tac o MATCH_MP qrel_sym)
      >> imp_res_tac qrel_cons_IMP
      >> rveq >> fs[]
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> match_mp_tac qrel_sym
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[] >> rpt(pairarg_tac >> fs[])
      >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rw[qrel_refl])
  >- (Cases_on `q1` >> fs[] >> rveq
      >> match_mp_tac qrel_queue_reorder >> rw[]));

val qrel_snocE = Q.store_thm("qrel_snocE",
  `!q1 q2 qe. qrel (SNOC qe q1) (SNOC qe q2) ==> qrel q1 q2`,
  `!qq1 qq2. qrel qq1 qq2 ==> (!q1 q2 qe. qq1 = (SNOC qe q1) /\ qq2 = (SNOC qe q2) ==> qrel q1 q2)`
    suffices_by metis_tac[qrel_refl]
  >> ho_match_mp_tac qrel_strongind >> rpt strip_tac
  >> fs[] >> rveq
  >- metis_tac[qrel_rules]
  >- metis_tac[qrel_rules]
  >- (imp_res_tac qrel_LENGTH
      >> qpat_x_assum `qrel _ (_ ++ _)` (assume_tac o MATCH_MP qrel_sym)
      >> imp_res_tac (qrel_snoc_IMP |> REWRITE_RULE [SNOC_APPEND])
      >> rveq >> fs[]
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> match_mp_tac qrel_sym
      >> match_mp_tac qrel_trans >> asm_exists_tac >> rw[]
      >> fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[] >> rpt(pairarg_tac >> fs[])
      >> fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)] >> rw[qrel_refl])
  >- (Q.ISPEC_THEN `q2` assume_tac SNOC_CASES >> fs[] >> rveq
      >> fs[] >> rveq
      >> match_mp_tac qrel_queue_reorder >> rw[]));

val qrel_append_r_E = Q.store_thm("qrel_append_r_E",
  `!q3 q1 q2. qrel (q1++q3) (q2++q3) ==> qrel q1 q2`,
  ho_match_mp_tac SNOC_INDUCT >> rpt strip_tac >> fs[APPEND_SNOC] >> metis_tac[qrel_snocE]);

val qrel_append_l_E = Q.store_thm("qrel_append_l_E",
  `!q1 q2 q3. qrel (q1++q2) (q1++q3) ==> qrel q2 q3`,
  Induct >> rpt strip_tac >> fs[] >> metis_tac[qrel_consE]);

val qcong_nil_rel_nil = Q.store_thm("qcong_nil_rel_nil",
  `!n2.
    qcong NNil n2
    ==> n2 = NNil`,
  `!n1 n2.
    qcong n1 n2
    ==> (n1 = NNil ==> n2 = NNil)
        /\ (n2 = NNil ==> n1 = NNil)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[]);

val qcong_endpoint_rel_endpoint = Q.store_thm("qcong_endpoint_rel_endpoint",
  `!p1 s1 e1 n2.
    qcong (NEndpoint p1 s1 e1) n2
    ==> ?s2. n2 = (NEndpoint p1 s2 e1)`,
  `!n1 n2.
    qcong n1 n2
    ==> (!p1 s1 e1. n1 = NEndpoint p1 s1 e1 ==> ?s2. n2 = NEndpoint p1 s2 e1)
        /\ (!p2 s2 e2. n2 = NEndpoint p2 s2 e2 ==> ?s1. n1 = NEndpoint p2 s1 e2)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[])

val qcong_par_rel_par = Q.store_thm("qcong_par_rel_par",
  `!n1 n2 n3.
    qcong (NPar n1 n2) n3
    ==> ?n4 n5. n3 = (NPar n4 n5) /\ qcong n1 n4 /\ qcong n2 n5`,
  `!n1 n2.
    qcong n1 n2
    ==> (!n3 n4. n1 = NPar n3 n4 ==> ?n5 n6. n2 = NPar n5 n6 /\ qcong n3 n5 /\ qcong n4 n6)
        /\ (!n3 n4. n2 = NPar n3 n4 ==> ?n5 n6. n1 = NPar n5 n6 /\ qcong n5 n3 /\ qcong n6 n4)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[qcong_refl,qcong_sym]
  >> rpt(first_x_assum drule >> strip_tac) >> metis_tac[qcong_rules]);

val qcong_par_rel_par_sym = Q.store_thm("qcong_par_rel_par_sym",
  `!n1 n2 n3.
    qcong n1 (NPar n2 n3)
    ==> ?n4 n5. n1 = (NPar n4 n5) /\ qcong n4 n2 /\ qcong n5 n3`,
  metis_tac[qcong_par_rel_par,qcong_sym]);

val qcong_bindings_eq = Q.store_thm("qcong_bindings_eq",
  `!p1 s1 e1 p2 s2 e2.
    qcong (NEndpoint p1 s1 e1) (NEndpoint p2 s2 e2)
    ==> s1.bindings = s2.bindings`,
  `!n1 n2.
    qcong n1 n2 ==>
    !p1 s1 e1 p2 s2 e2.
    n1 = NEndpoint p1 s1 e1 /\ n2 = NEndpoint p2 s2 e2
    ==> s1.bindings = s2.bindings` suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[] >> rveq >> simp[]
  >> metis_tac[qrel_rules,qcong_endpoint_rel_endpoint]);

val qcong_IMP_qrel = Q.store_thm("qcong_IMP_qrel",
  `!p1 s1 e1 p2 s2 e2.
    qcong (NEndpoint p1 s1 e1) (NEndpoint p2 s2 e2)
    ==> qrel s1.queue s2.queue`,
  `!n1 n2.
    qcong n1 n2 ==>
    !p1 s1 e1 p2 s2 e2.
    n1 = NEndpoint p1 s1 e1 /\ n2 = NEndpoint p2 s2 e2
    ==> qrel s1.queue s2.queue` suffices_by metis_tac[]
  >> ho_match_mp_tac qcong_strongind >> rpt strip_tac
  >> rveq >> fs[] >> rveq >> simp[]
  >> metis_tac[qrel_rules,qcong_endpoint_rel_endpoint]);

val qcong_queue_reorder'' = Q.store_thm("qcong_queue_reorder''",
  `∀p e p1 d1 p2 d2 b q1 q2.
     p1 ≠ p2
     ⇒ qcong (NEndpoint p (<|bindings := b; queue:=q1 ++ [(p1,d1);(p2,d2)] ++ q2|>) e)
              (NEndpoint p (<|bindings := b; queue:= q1 ++ [(p2,d2);(p1,d1)] ++ q2|>) e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `qcong (NEndpoint _ a1 _) (NEndpoint _ (<|bindings := _; queue := a2|>) _)`
  >> `<|bindings := b; queue := a2|> = a1 with queue := a2` by(unabbrev_all_tac >> fs[])
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac qcong_queue_reorder
  >> simp[]);

val qcong_endpoints = Q.store_thm("qcong_endpoints",
  `!n1 n2. qcong n1 n2 ==> MAP FST (endpoints n2) = MAP FST (endpoints n1)`,
  ho_match_mp_tac qcong_strongind >> rw[endpoints_def])

val qcong_sym_eq = Q.store_thm("qcong_sym_eq",
`∀p q. qcong p q = qcong q p`,metis_tac[qcong_sym]);

val qcong_trans_eq = Q.store_thm("qcong_trans_eq",
  `∀p1 q1 .
     qcong p1 q1
     ⇒ ∀ alpha p2 q2.
            ((trans p1 alpha p2 ⇒ (∃q2. trans q1 alpha q2 ∧ qcong p2 q2))
         ∧ (trans q1 alpha q2 ⇒ (∃p2. trans p1 alpha p2 ∧ qcong p2 q2)))`,
  ho_match_mp_tac qcong_strongind
  >> rpt strip_tac
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- (* qcong_queue_reorder *)
     (‘∃pp. pp = NEndpoint p s e’ by simp[]
      >> pop_assum(fn thm => SUBST_ALL_TAC(GSYM thm) >> mp_tac thm)
      >> qhdtm_x_assum ‘trans’ (fn thm => rpt(pop_assum mp_tac) >> assume_tac thm)
      >> MAP_EVERY qid_spec_tac [‘e’,‘p’,‘s’]
      >> pop_assum mp_tac
      >> MAP_EVERY qid_spec_tac [‘p2'’,‘alpha’,‘pp’]
      >> ho_match_mp_tac trans_ind
      >> rw[] >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := q1 ⧺ [(p2,d2); (p1,d1)] ⧺ q2) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> fs[])
             >- metis_tac[qcong_rules])
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with queue := SNOC a3 _) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC a3 (q1 ++ [(p2,d2);(p1,d1)] ++ q2)) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac [trans_enqueue',trans_enqueue_choice_l',trans_enqueue_choice_r']
                 >> simp[])
             >- (simp[SNOC_APPEND] >> metis_tac[qcong_queue_reorder',APPEND_ASSOC]))
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with bindings := a3) a4)`
              >> qexists_tac `NEndpoint a1 ((a2 with queue := (q1 ++ [(p2,d2);(p1,d1)] ++ q2))
                                                with bindings := a3) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> `s.bindings = (s with queue := q1 ++ [(p2,d2); (p1,d1)] ++ q2).bindings`
                       by simp[]
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
                 >> match_mp_tac trans_let
                 >> simp[])
             >- (`(a2 with bindings := a3).queue = a2.queue` by fs[]
                 >> PURE_ONCE_REWRITE_TAC [GSYM endpointLangTheory.state_fupdcanon]
                 >> metis_tac [qcong_queue_reorder]))
      >> TRY(rename1 `Receive`
             >> fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[Once APPEND_EQ_CONS]
             >> fs[APPEND_EQ_SING] >> rveq >> fs[] >> rveq >> fs[]
             >> rw[Once trans_cases,PULL_EXISTS]
             >> qexists_tac `d`
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2)]` >>
                    rw[qcong_refl] >>
                    NO_TAC
                   )
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _ ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2);(p1,d1)] ++ l` >>
                    rw[] >>
                    metis_tac[qcong_queue_reorder'',qcong_refl,APPEND_ASSOC,APPEND] >>
                    NO_TAC
                   )
             >> HINT_EXISTS_TAC
             >> rw[]
             >> metis_tac[qcong_queue_reorder'',qcong_refl,APPEND_ASSOC,APPEND])
      >> TRY(fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[Once APPEND_EQ_CONS]
             >> fs[APPEND_EQ_SING] >> rveq >> fs[] >> rveq >> fs[]
             >> Q.REFINE_EXISTS_TAC `NEndpoint _ _ _`
             >> rw[Once trans_cases,PULL_EXISTS,EXISTS_OR_THM,RIGHT_AND_OVER_OR]
             >> ((qmatch_asmsub_abbrev_tac `_ <> [1w]` >> disj2_tac) ORELSE disj1_tac)
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2)]` >>
                    rw[qcong_refl] >>
                    NO_TAC
                   )
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _ ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2);(p1,d1)] ++ l` >>
                    rw[] >>
                    metis_tac[qcong_queue_reorder',qcong_refl,APPEND_ASSOC,APPEND]
                   )
             >> HINT_EXISTS_TAC
             >> rw[]
             >> metis_tac[qcong_queue_reorder',qcong_refl,APPEND_ASSOC,APPEND])
      >> TRY(rename1 ‘dsubst’ >> metis_tac[trans_fix,qcong_rules])
     )
  >- (* qcong_queue_reorder, symmetric case *)
     (qmatch_asmsub_abbrev_tac `NEndpoint _ s' _`
      >> `s'.queue = q1 ⧺ [(p2,d2); (p1,d1)] ⧺ q2` by(unabbrev_all_tac >> simp[])
      >> `s = s' with queue := q1 ⧺ [(p1,d1); (p2,d2)] ⧺ q2`
            by(unabbrev_all_tac >> simp[endpointLangTheory.state_component_equality])
      >> pop_assum (fn thm => fs[thm])
      >> qpat_x_assum `Abbrev _` kall_tac
      >> rename1 `s with queue := _ ++ [(p3,d3); (p4,d4)] ++ _`
      >> rename1 `_ with queue := _ ++ [(p2,d2); (p1,d1)] ++ _`
      >> PURE_ONCE_REWRITE_TAC [qcong_sym_eq]
      >> ‘∃pp. pp = NEndpoint p s e’ by simp[]
      >> pop_assum(fn thm => SUBST_ALL_TAC(GSYM thm) >> mp_tac thm)
      >> qhdtm_x_assum ‘trans’ (fn thm => rpt(pop_assum mp_tac) >> assume_tac thm)
      >> MAP_EVERY qid_spec_tac [‘e’,‘p’,‘s’]
      >> pop_assum mp_tac
      >> MAP_EVERY qid_spec_tac [‘q2'’,‘alpha’,‘pp’]
      >> ho_match_mp_tac trans_ind
      >> rw[] >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := q1 ⧺ [(p2,d2); (p1,d1)] ⧺ q2) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> fs[])
             >- metis_tac[qcong_rules])
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with queue := SNOC a3 _) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC a3 (q1 ++ [(p2,d2);(p1,d1)] ++ q2)) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac [trans_enqueue',trans_enqueue_choice_l',trans_enqueue_choice_r']
                 >> simp[])
             >- (simp[SNOC_APPEND] >> metis_tac[qcong_queue_reorder',APPEND_ASSOC]))
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with bindings := a3) a4)`
              >> qexists_tac `NEndpoint a1 ((a2 with queue := (q1 ++ [(p2,d2);(p1,d1)] ++ q2))
                                                with bindings := a3) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> `s.bindings = (s with queue := q1 ++ [(p2,d2); (p1,d1)] ++ q2).bindings`
                       by simp[]
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
                 >> match_mp_tac trans_let
                 >> simp[])
             >- (`(a2 with bindings := a3).queue = a2.queue` by fs[]
                 >> PURE_ONCE_REWRITE_TAC [GSYM endpointLangTheory.state_fupdcanon]
                 >> metis_tac [qcong_queue_reorder]))
      >> TRY(rename1 `Receive`
             >> fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[Once APPEND_EQ_CONS]
             >> fs[APPEND_EQ_SING] >> rveq >> fs[] >> rveq >> fs[]
             >> rw[Once trans_cases,PULL_EXISTS]
             >> qexists_tac `d`
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2)]` >>
                    rw[qcong_refl] >>
                    NO_TAC
                   )
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _ ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2);(p1,d1)] ++ l` >>
                    rw[] >>
                    metis_tac[qcong_queue_reorder'',qcong_refl,APPEND_ASSOC,APPEND] >>
                    NO_TAC
                   )
             >> HINT_EXISTS_TAC
             >> rw[]
             >> metis_tac[qcong_queue_reorder'',qcong_refl,APPEND_ASSOC,APPEND])
      >> TRY(fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[Once APPEND_EQ_CONS]
             >> fs[APPEND_EQ_SING] >> rveq >> fs[] >> rveq >> fs[]
             >> Q.REFINE_EXISTS_TAC `NEndpoint _ _ _`
             >> rw[Once trans_cases,PULL_EXISTS,EXISTS_OR_THM,RIGHT_AND_OVER_OR]
             >> ((qmatch_asmsub_abbrev_tac `_ <> [1w]` >> disj2_tac) ORELSE disj1_tac)
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2)]` >>
                    rw[qcong_refl] >>
                    NO_TAC
                   )
             >> TRY(qmatch_goalsub_abbrev_tac `_ ++ [(_,_); (_,_)] ++ _ ++ _` >>
                    qexists_tac `q1 ++ [(p2,d2);(p1,d1)] ++ l` >>
                    rw[] >>
                    metis_tac[qcong_queue_reorder',qcong_refl,APPEND_ASSOC,APPEND]
                   )
             >> HINT_EXISTS_TAC
             >> rw[]
             >> metis_tac[qcong_queue_reorder',qcong_refl,APPEND_ASSOC,APPEND])
      >> TRY(rename1 ‘dsubst’ >> metis_tac[trans_fix,qcong_rules]))
  >- (qpat_x_assum `trans (NPar _ _) _ _` (assume_tac
                                           o REWRITE_RULE [Once trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_com_choice_l
      >> imp_res_tac trans_com_choice_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[qcong_rules])
  >- (qpat_x_assum `trans (NPar _ _) _ _` (assume_tac
                                           o REWRITE_RULE [Once trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_com_choice_l
      >> imp_res_tac trans_com_choice_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[qcong_rules]));

val qcong_trans_pres = Q.store_thm("qcong_trans_pres",
  `∀p1 q1 alpha p2.
     qcong p1 q1 ∧ trans p1 alpha p2
     ⇒ ∃q2. trans q1 alpha q2 ∧ qcong p2 q2`,
  metis_tac[qcong_trans_eq])

val list_trans_def = Define `
    (list_trans p [] q = (p = q))
 /\ (list_trans p (alpha::l) q = ?p'. trans p alpha p' /\ list_trans p' l q)`

val list_trans_append = Q.store_thm("list_trans_append",
  `!l1 n1 l2 n2. list_trans n1 (l1 ++ l2) n2 =
  ?n3. list_trans n1 l1 n3 /\ list_trans n3 l2 n2`,
  Induct_on `l1` >> rpt strip_tac >> fs[list_trans_def]
  >> rw[EQ_IMP_THM] >> fs[] >> metis_tac[]);

val list_trans_par_l = Q.store_thm("list_trans_par_l",
  `∀conf p alpha q r. list_trans p alpha q ==> list_trans (NPar p r) alpha (NPar q r)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[endpointSemTheory.trans_par_l]);

val list_trans_par_r = Q.store_thm("list_trans_par_r",
  `∀conf p alpha q r. list_trans p alpha q ==> list_trans (NPar r p) alpha (NPar r q)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[endpointSemTheory.trans_par_r]);

val endpoint_names_trans = Q.store_thm("endpoint_names_trans",
  `!n1 alpha n2. trans n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  ho_match_mp_tac trans_strongind >> rpt strip_tac >> fs[endpoints_def]);

val endpoint_names_list_trans = Q.store_thm("endpoint_names_list_trans",
  `!n1 alpha n2. list_trans n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  Induct_on `alpha` >> rw[list_trans_def] >>
  metis_tac[endpoint_names_trans]);

val sender_is_endpoint = Q.store_thm("sender_is_endpoint",
 `∀p1 p2 q1 d q2.
  trans p1 (LSend q1 d q2) p2 ==> MEM q1 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val choice_sender_is_endpoint = Q.store_thm("choice_sender_is_endpoint",
 `∀p1 p2 q1 d q2.
  trans p1 (LIntChoice q1 d q2) p2 ==> MEM q1 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val choice_receiver_is_endpoint = Q.store_thm("choice_receiver_is_endpoint",
 `∀p1 p2 q1 d q2.
  trans p1 (LExtChoice q1 d q2) p2 ==> MEM q2 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val receiver_is_endpoint = Q.store_thm("receiver_is_endpoint",
 `∀p1 p2 q1 d q2.
  trans p1 (LReceive q1 d q2) p2 ==> MEM q2 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val free_names_are_names_endpoint = Q.store_thm("free_names_are_names_endpoint",
  `!e v. MEM v (free_var_names_endpoint e) ==> MEM v (var_names_endpoint e)`,
  Induct >> rpt strip_tac
  >> fs[var_names_endpoint_def,free_var_names_endpoint_def,MEM_FILTER]);

val free_names_are_names = Q.store_thm("free_names_are_names",
  `!n v. MEM v (free_var_names_network n) ==> MEM v (var_names_network n)`,
  Induct >> rpt strip_tac
  >> fs[var_names_network_def,free_var_names_network_def,free_names_are_names_endpoint]);

val trans_var_names_mono = Q.store_thm("trans_var_names_mono",
  `!n1 alpha n2 fv.
    trans n1 alpha n2
    ∧ MEM fv (var_names_network n2) ==> MEM fv (var_names_network n1)`,
  rpt strip_tac
  >> qpat_x_assum `MEM _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`alpha`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> fs[var_names_network_def,var_names_endpoint_def]
  >> res_tac
  >> imp_res_tac MEM_var_names_endpoint_dsubst
  >> fs[var_names_endpoint_def]);

val reduction_var_names_mono = Q.store_thm("reduction_var_names_mono",
  `!n1 n2 fv.
    reduction^* n1 n2
    ∧ MEM fv (var_names_network n2) ==> MEM fv (var_names_network n1)`,
  rpt strip_tac
  >> qpat_x_assum `MEM _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`fv`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`n1`]
  >> ho_match_mp_tac RTC_ind
  >> rpt strip_tac
  >> fs [reduction_def] >> drule trans_var_names_mono
  >> rw []);

val partners_endpoint_def = Define `
   (partners_endpoint Nil = [])
∧ (partners_endpoint (Send p v e) = p::(partners_endpoint e))
∧ (partners_endpoint (Receive p v e) = p::(partners_endpoint e))
∧ (partners_endpoint (IntChoice b p e) =
    p::(partners_endpoint e))
∧ (partners_endpoint (ExtChoice p e1 e2) =
    p::((partners_endpoint e1) ++ (partners_endpoint e2)))
∧ (partners_endpoint (IfThen v e1 e2) = (partners_endpoint e1) ++ (partners_endpoint e2))
∧ (partners_endpoint (Let v f vl e) = partners_endpoint e)
∧ (partners_endpoint (Fix dn e) = partners_endpoint e)
∧ (partners_endpoint (Call dn) = [])`

val partners_network_def = Define `
   (partners_network NNil = [])
∧ (partners_network (NPar n1 n2) = (partners_network n1 ++ partners_network n2))
∧ (partners_network (NEndpoint p s e) = (partners_endpoint e))`

Theorem partners_endpoint_dsubst:
  MEM x (partners_endpoint(dsubst e dn e')) ⇒
  MEM x (partners_endpoint e') ∨ MEM x (partners_endpoint e)
Proof
  Induct_on ‘e’ >> rw[partners_endpoint_def,dsubst_def] >>
  res_tac >> fs[]
QED


val closed_under_def = Define `
  closed_under s n = (set(partners_network n) ⊆ s)`

val closed_network_def = Define `
  closed_network n = closed_under (set(MAP FST (endpoints n))) n`

val endpoint_ok_def = Define `
  endpoint_ok (n,s,e) = ~MEM n (partners_endpoint e)`

val weak_trans_refl = Q.store_thm("weak_trans_refl",
  `!n. weak_trans n LTau n`,
  rw[weak_trans_def]);

val closed_under_junkcong = Q.store_thm("closed_under_junkcong",
  `!fvs n1 n2 e. junkcong fvs n1 n2 /\ set (MAP FST (endpoints n1)) ⊆ e ==> closed_under e n1 = closed_under e n2`,
  Induct_on `n1`
  >> rpt strip_tac
  >> imp_res_tac junkcong_endpoint_rel_endpoint
  >> imp_res_tac junkcong_par_rel_par
  >> imp_res_tac junkcong_nil_rel_nil
  >> fs[closed_network_def] >> rveq >> fs[closed_under_def,partners_network_def,endpoints_def]
  >> metis_tac[]);

val closed_network_junkcong = Q.store_thm("closed_network_junkcong",
  `!fvs n1 n2 e. junkcong fvs n1 n2 ==> closed_network n1 = closed_network n2`,
  rpt strip_tac >> drule closed_under_junkcong
  >> disch_then(qspec_then `set (MAP FST (endpoints n1))` mp_tac)
  >> impl_tac >- MATCH_ACCEPT_TAC SUBSET_REFL
  >> simp[closed_network_def] >> imp_res_tac junkcong_endpoints
  >> rw[]);

val closed_under_receiver_mem = Q.store_thm("closed_under_receiver_mem",
  `!n1 p1 d p2 n2 e.
     trans n1 (LSend p1 d p2) n2 /\ closed_under e n1
      /\ set (MAP FST (endpoints n1)) ⊆ e
     ==> p2 ∈ e
  `,
  rpt strip_tac
  >> ntac 2 (pop_assum mp_tac)
  >> qmatch_asmsub_abbrev_tac `trans _ a1 _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p1`,`p2`,`d`,`e`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`a1`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def,closed_under_def,partners_endpoint_def,partners_network_def]
  >> first_x_assum(drule_at_then (Pos last) match_mp_tac)
  >> fs[SUBSET_DEF] >> rw[]
  >> imp_res_tac partners_endpoint_dsubst
  >> fs[partners_endpoint_def]);

val closed_network_receiver_mem = Q.store_thm("closed_network_receiver_mem",
  `!n1 p1 d p2 n2 e.
     trans n1 (LSend p1 d p2) n2 /\ closed_network n1
     ==> MEM p2 (MAP FST (endpoints n1))
  `,
  rpt strip_tac
  >> fs[closed_network_def]
  >> imp_res_tac closed_under_receiver_mem
  >> fs[]);

val var_names_endpoint_in_network = Q.store_thm("var_names_endpoint_in_network",
  `!fv e n. MEM fv (var_names_endpoint (SND(SND(e))))
            /\ MEM e (endpoints n) ==> MEM fv (var_names_network n)`,
  Induct_on `n` >> rpt strip_tac >> fs[var_names_network_def,endpoints_def]
  >> metis_tac[]);

val free_var_names_endpoint_in_network = Q.store_thm("free_var_names_endpoint_in_network",
  `!fv e n. MEM fv (free_var_names_endpoint (SND(SND(e))))
            /\ MEM e (endpoints n) ==> MEM fv (free_var_names_network n)`,
  Induct_on `n` >> rpt strip_tac >> fs[free_var_names_network_def,endpoints_def]
  >> metis_tac[]);

val endpoint_names_reduction = Q.store_thm("endpoint_names_reduction",
  `!n1 n2. reduction^* n1 n2 ==> MAP FST (endpoints n2) = MAP FST (endpoints n1)`,
  PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ]
  >> ho_match_mp_tac RTC_lifts_reflexive_transitive_relations
  >> rpt strip_tac >> fs[reduction_def] >> imp_res_tac endpoint_names_trans
  >> fs[reflexive_def,transitive_def]);

val junkcong_var_names = Q.store_thm("junkcong_var_names",
  `!fvs n1 n2. junkcong fvs n1 n2 ==> var_names_network n1 = var_names_network n2`,
  ho_match_mp_tac junkcong_ind >> rpt strip_tac
  >> fs[var_names_network_def]);

val junkcong_free_var_names = Q.store_thm("junkcong_free_var_names",
  `!fvs n1 n2. junkcong fvs n1 n2 ==> free_var_names_network n1 = free_var_names_network n2`,
  ho_match_mp_tac junkcong_ind >> rpt strip_tac
  >> fs[free_var_names_network_def]);

val trans_endpoints_ok = Q.store_thm("trans_endpoints_ok",
  `!n1 alpha n2. trans n1 alpha n2
                 ==> EVERY endpoint_ok (endpoints n1)
                 ==> EVERY endpoint_ok (endpoints n2)`,
  ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[endpoints_def,endpoint_ok_def,partners_endpoint_def]
  >> spose_not_then strip_assume_tac
  >> imp_res_tac partners_endpoint_dsubst
  >> fs[partners_endpoint_def]);

val reduction_endpoints_ok = Q.store_thm("reduction_endpoints_ok",
  `!n1 n2. reduction^* n1 n2 /\ EVERY endpoint_ok (endpoints n1)
                 ==> EVERY endpoint_ok (endpoints n2)`,
  PURE_ONCE_REWRITE_TAC [CONJ_SYM]
  >> ho_match_mp_tac RTC_lifts_invariants
  >> metis_tac[trans_endpoints_ok,reduction_def]);

val closed_under_trans = Q.store_thm("closed_under_trans",
  `!n1 alpha n2 e. trans n1 alpha n2 /\ closed_under e n1 ==> closed_under e n2`,
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
  >> ho_match_mp_tac trans_ind
  >> rpt strip_tac >> fs[closed_under_def,partners_network_def,partners_endpoint_def]
  >> fs[SUBSET_DEF] >> rw[] >> imp_res_tac partners_endpoint_dsubst
  >> last_x_assum(match_mp_tac o MP_CANON)
  >> simp[]
  >> rw[]
  >> imp_res_tac partners_endpoint_dsubst
  >> fs[partners_endpoint_def]);

val closed_network_trans = Q.store_thm("closed_network_trans",
  `!n1 alpha n2. trans n1 alpha n2 /\ closed_network n1 ==> closed_network n2`,
  rpt strip_tac
  >> fs[closed_network_def]
  >> imp_res_tac endpoint_names_trans
  >> fs[]
  >> imp_res_tac closed_under_trans);

val closed_network_reduction = Q.store_thm("closed_network_reduction",
  `!n1 n2. reduction^* n1 n2 /\ closed_network n1 ==> closed_network n2`,
  simp[Once CONJ_SYM]
  >> ho_match_mp_tac RTC_lifts_invariants
  >> simp[Once CONJ_SYM, reduction_def]
  >> MATCH_ACCEPT_TAC closed_network_trans);

Theorem choice_free_endpoint_dsubst_IMP:
  choice_free_endpoint (dsubst e dn e') ⇒
  choice_free_endpoint e
Proof
  Induct_on ‘e’ >> rw[choice_free_endpoint_def,dsubst_def]
QED

Theorem choice_free_endpoint_dsubstI:
  choice_free_endpoint e ∧ choice_free_endpoint e' ⇒
  choice_free_endpoint (dsubst e dn e')
Proof
  Induct_on ‘e’ >> rw[choice_free_endpoint_def,dsubst_def]
QED

val choice_free_network_no_choice = Q.store_thm("choice_free_network_no_choice",
  `!n1 n2 p1 b p2. trans n1 (LIntChoice p1 b p2) n2 /\ choice_free_network n1 ==> F`,
  rpt GEN_TAC
  >> qmatch_goalsub_abbrev_tac `trans _ a1 _`
  >> rpt strip_tac
  >> pop_assum mp_tac
  >> qpat_x_assum `Abbrev _` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`b`,`p1`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`a1`,`n1`]
  >> ho_match_mp_tac trans_ind >> rw[choice_free_network_def,choice_free_endpoint_def]
  >> metis_tac[choice_free_endpoint_dsubstI,choice_free_endpoint_def]);

val choice_free_trans_pres = Q.store_thm("choice_free_trans_pres",
  `!n1 alpha n2. trans n1 alpha n2 /\ choice_free_network n1 ==> choice_free_network n2`,
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
   >> ho_match_mp_tac trans_ind >> rw[choice_free_network_def,choice_free_endpoint_def]
  >> metis_tac[choice_free_endpoint_dsubstI,choice_free_endpoint_def]);

val choice_free_reduction = Q.store_thm("choice_free_reduction",
  `!n1 n2. reduction^* n1 n2 /\ choice_free_network n1 ==> choice_free_network n2`,
  simp[Once CONJ_SYM] >> ho_match_mp_tac RTC_lifts_invariants
  >> metis_tac[choice_free_trans_pres,reduction_def]);

val sender_receiver_distinct_choice = Q.store_thm("sender_receiver_distinct_choice",
  `!n1 p1 b p2 n2.
     trans n1 (LIntChoice p1 b p2) n2 ==> p1 ≠ p2`,
  rpt strip_tac >> pop_assum mp_tac
  >> qmatch_asmsub_abbrev_tac `trans _ a1 _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p1`,`b`,`p2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`a1`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[]);

val sender_receiver_distinct = Q.store_thm("sender_receiver_distinct",
  `!n1 p1 d p2 n2.
     trans n1 (LSend p1 d p2) n2 ==> p1 ≠ p2`,
  rpt strip_tac >> pop_assum mp_tac
  >> qmatch_asmsub_abbrev_tac `trans _ a1 _`
  >> pop_assum (mp_tac o PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p1`,`d`,`p2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n2`,`a1`,`n1`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[]);

Theorem trans_same_sender_determ:
  trans p1 (LSend q2 d1 q1) p2
  /\ trans p1 (LSend q2 d2 q3) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> q1 = q3 /\ d1 = d2 /\ p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`q2`,`d2`,`q1`,`d1`,`p3`,`q3`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[sender_is_endpoint]
QED

Theorem trans_same_sender_choice_determ:
  trans p1 (LIntChoice q2 d1 q1) p2
  /\ trans p1 (LIntChoice q2 d2 q3) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> q1 = q3 /\ d1 = d2 /\ p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`q2`,`d2`,`q1`,`d1`,`p3`,`q3`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[choice_sender_is_endpoint]
QED

Theorem trans_same_receiver_determ:
  trans p1 (LReceive s d r) p2
  /\ trans p1 (LReceive s d r) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`p3`,`s`,`d`,`r`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> TRY(rename1 ‘NEndpoint’
         >> ‘∃pp. pp = NEndpoint p2 s e’ by simp[]
         >> ‘∃alpha. alpha = LReceive p1 d p2’ by simp[]
         >> pop_assum(fn thm => SUBST_ALL_TAC(GSYM thm) >> mp_tac thm)
         >> pop_assum(fn thm => SUBST_ALL_TAC(GSYM thm) >> mp_tac thm)
         >> qhdtm_x_assum ‘trans’ (fn thm => rpt(pop_assum mp_tac) >> assume_tac thm)
         >> qid_spec_tac ‘e’
         >> pop_assum mp_tac
         >> MAP_EVERY qid_spec_tac [‘p3’,‘alpha’,‘pp’]
         >> ho_match_mp_tac trans_ind
         >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
         >> rw[]
         >> metis_tac[])
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[receiver_is_endpoint]
QED

Theorem trans_same_receiver_choice_determ:
  trans p1 (LExtChoice s b r) p2
  /\ trans p1 (LExtChoice s b r) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`p3`,`s`,`b`,`r`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[choice_receiver_is_endpoint]
QED

Theorem trans_send_choice_distinct_senders:
  trans p1 (LSend q2 d1 q1) p2
  /\ trans p1 (LIntChoice q3 b q4) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> q2 <> q3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`q4`,`q2`,`d2`,`q1`,`d1`,`p3`,`q3`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[sender_is_endpoint,choice_sender_is_endpoint]
QED

Theorem trans_no_selfloop:
  !p1 alpha p2.
  trans p1 alpha p2 ∧ alpha ≠ LTau
  ==> p1 <> p2
Proof
  PURE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_ind >> rw[] >> fs[endpointLangTheory.state_component_equality] >>
  TRY(disj2_tac) >> spose_not_then strip_assume_tac >>
  qmatch_asmsub_abbrev_tac `a1 = a2` >>
  `endpoint_size a1 = endpoint_size a2` by simp[] >>
  pop_assum mp_tac >> unabbrev_all_tac >> rpt(pop_assum kall_tac) >>
  simp[endpoint_size_def]
QED

Theorem trans_different_sender:
  trans p1 (LSend s1 d1 r1) p2
  /\ trans p1 (LSend s2 d2 r2) p3
  /\ s1 <> s2
  ==> p2 <> p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`r2`,`r1`,`d2`,`s2`,`d1`,`p3`,`s1`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[sender_is_endpoint,trans_no_selfloop]
QED

Theorem trans_send_receive_distinct:
  trans p1 (LSend s1 d1 r1) p2
  /\ trans p1 (LReceive s2 d2 r2) p3
  ==> p2 <> p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`r2`,`r1`,`d2`,`s2`,`d1`,`p3`,`s1`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> fs[endpointLangTheory.state_component_equality]
  >> metis_tac[sender_is_endpoint,trans_no_selfloop]
QED

val receive_ext_choice_rel_def = Define
  `receive_ext_choice_rel alpha beta =
   ?s d r b.
    alpha = LReceive s d r /\ beta = LExtChoice s b r /\
    d = if b then [1w] else [0w]`

val label_rel_def = Define `
 label_rel alpha beta =
 (alpha = beta \/ receive_ext_choice_rel alpha beta \/ receive_ext_choice_rel beta alpha)
 `

Theorem trans_send_receive_distinct:
  trans p1 (LSend s1 d1 r1) p2
  /\ trans p1 (LReceive s2 d2 r2) p3
  ==> p2 <> p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`r2`,`r1`,`d2`,`s2`,`d1`,`p3`,`s1`,`p2`,`alpha`,`p1`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> fs[endpointLangTheory.state_component_equality]
  >> metis_tac[sender_is_endpoint,trans_no_selfloop]
QED

Theorem trans_no_selfloop'[simp]:
  (trans p1 (LReceive p2 d p3) p1 <=> F) ∧
  (trans p1 (LSend p2 d p3) p1 <=> F) ∧
  (trans p1 (LIntChoice p2 b p3) p1 <=> F) ∧
  (trans p1 (LExtChoice p2 b p3) p1 <=> F)
Proof
  metis_tac[trans_no_selfloop,label_distinct]
QED

Theorem trans_selfloop_LTau:
  trans p1 alpha p1 ⇒ alpha = LTau
Proof
  metis_tac[trans_no_selfloop,label_distinct]
QED

Theorem trans_distinct_residual:
  !p1 alpha p2 beta p3.
  trans p1 alpha p2
  /\ trans p1 beta p3
  /\ ~label_rel alpha beta
  ==> p2 <> p3
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_strongind >> rpt strip_tac >>
  fs[] >> rveq >>
  qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
  fs[] >> rveq >> fs[] >> rveq >>
  fs[endpointLangTheory.state_component_equality,
     label_rel_def,label_rel_def,receive_ext_choice_rel_def] >>
  TRY(qmatch_asmsub_abbrev_tac `a1 = (a2:endpoint)` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      fs[Abbr `a1`, Abbr `a2`,endpoint_size_def] >>
      NO_TAC
      ) >>
  metis_tac[trans_selfloop_LTau]
QED

Definition join_endpoint_def:
  (join_endpoint Nil Nil = SOME Nil) /\
  (join_endpoint (Send p1 v1 e1) (Send p2 v2 e2) =
   if p1 = p2 /\ v1 = v2 then
     OPTION_BIND (join_endpoint e1 e2) (SOME o Send p1 v2)
   else NONE) /\
  (join_endpoint (Receive p1 v1 e1) (Receive p2 v2 e2) =
   if p1 = p2 /\ v1 = v2 then
     OPTION_BIND (join_endpoint e1 e2) (SOME o Receive p1 v2)
   else NONE) /\
  (join_endpoint (IntChoice b1 p1 e1) (IntChoice b2 p2 e2) =
   if p1 = p2 /\ b1 = b2 then
     OPTION_BIND (join_endpoint e1 e2) (SOME o IntChoice b1 p1)
   else NONE) /\
  (join_endpoint (IfThen v1 e1 e2) (IfThen v2 e3 e4) =
   if v1 = v2 then
     case (join_endpoint e1 e3, join_endpoint e2 e4) of
       (SOME e5, SOME e6) => SOME(IfThen v1 e5 e6)
     | _ => NONE
    else NONE) /\
  (join_endpoint (Let v1 f1 l1 e1) (Let v2 f2 l2 e2) =
     if v1 = v2 /\ f1 = f2 /\ l1 = l2 then
       OPTION_BIND (join_endpoint e1 e2) (SOME o Let v1 f1 l1)
     else NONE) /\
  (join_endpoint (ExtChoice p1 e1 e2) (ExtChoice p2 e3 e4) =
   if p1 = p2 then
    (case (join_endpoint e1 e3, join_endpoint e2 e4) of
        (SOME e5, SOME e6) => SOME(ExtChoice p1 e5 e6)
      | (SOME e5, NONE) =>
        if e2 = Nil then
          SOME(ExtChoice p1 e5 e4)
        else if e4 = Nil then
          SOME(ExtChoice p1 e5 e2)
        else NONE
      | (NONE, SOME e6) =>
        if e1 = Nil then
          SOME(ExtChoice p1 e3 e6)
        else if e3 = Nil then
          SOME(ExtChoice p1 e1 e6)
        else NONE
      | (NONE,NONE) =>
        if (e1 = Nil \/ e3 = Nil) /\ (e2 = Nil \/ e4 = Nil) then
          SOME(ExtChoice p1
                (if e1 = Nil then e3 else e1)
                (if e2 = Nil then e4 else e2)
              )
        else NONE
      | _ => NONE)
   else NONE) /\
  (join_endpoint (Call dn) (Call dn') =
   (if dn = dn' then SOME(Call dn') else NONE)) /\
  (join_endpoint (Fix dn e1) (Fix dn' e2) =
   (if dn = dn' then
     case join_endpoint e1 e2 of
       SOME e3 => SOME(Fix dn' e3)
     | _ => NONE
    else NONE)) /\
  (join_endpoint _ _ = NONE)
End

Theorem join_endpoint_NilNONE[simp]:
  (join_endpoint Nil e = NONE ⇔ e ≠ Nil) ∧
  (join_endpoint e Nil = NONE ⇔ e ≠ Nil)
Proof
  Cases_on ‘e’ >> simp[join_endpoint_def]
QED

Definition join_network_def:
 (join_network (NPar n1 n2) (NPar n3 n4) =
   (case (join_network n1 n3, join_network n2 n4) of
      (SOME n5, SOME n6) => SOME(NPar n5 n6)
    | _ => NONE)) /\
 (join_network NNil NNil =
   SOME NNil) /\
 (join_network (NEndpoint p1 s1 e1) (NEndpoint p2 s2 e2) =
   if p1 = p2 /\ s1 = s2 then
     OPTION_BIND (join_endpoint e1 e2) (SOME o NEndpoint p1 s1)
   else NONE) /\
  (join_network _ _ = NONE)
End

Theorem join_endpoint_nilSOME[simp]:
  (join_endpoint e Nil = SOME x ⇔ e = Nil ∧ x = Nil) ∧
  (join_endpoint Nil e = SOME x ⇔ e = Nil ∧ x = Nil) ∧
  (join_endpoint e1 e2 = SOME Nil ⇔ e1 = Nil ∧ e2 = Nil)
Proof
  rpt strip_tac >~ [‘join_endpoint _ _ = SOME Nil’]
  >- (map_every Cases_on [‘e1’,‘e2’] >> simp[join_endpoint_def, AllCaseEqs()])>>
  Cases_on ‘e’ >> simp[join_endpoint_def, EQ_SYM_EQ]
QED

Theorem join_endpoint_nil:
  join_endpoint e Nil = SOME Nil ==> e = Nil
Proof
  simp[]
QED

Theorem join_endpoint_nil_not_nil:
  e <> Nil ==>
  join_endpoint e Nil = NONE /\ join_endpoint Nil e = NONE
Proof
  simp[]
QED

Theorem join_endpoint_sym:
  !e1 e2. join_endpoint e1 e2 = join_endpoint e2 e1
Proof
  recInduct (fetch "-" "join_endpoint_ind") \\
  rpt strip_tac \\
  PURE_ONCE_REWRITE_TAC[join_endpoint_def] \\
  fs[]
  >- (metis_tac[])
  >- (metis_tac[])
  >- (reverse IF_CASES_TAC >- metis_tac[] \\
      rw[] \\ metis_tac[])
  >- (reverse IF_CASES_TAC >- metis_tac[] \\
      rw[] \\ metis_tac[])
  >- (reverse IF_CASES_TAC >- metis_tac[] \\
      rw[] \\ metis_tac[])
  >- (reverse IF_CASES_TAC >- metis_tac[] \\
      rw[] >> rw[] >> fs[] >>
      rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) \\
      imp_res_tac join_endpoint_nil_not_nil \\
      fs[] \\ rfs[])
  >- (reverse IF_CASES_TAC >- metis_tac[] \\
      rw[])
  >- (reverse IF_CASES_TAC >- metis_tac[] \\
      rw[] \\ metis_tac[])
QED

Theorem join_endpoint_nil_sym:
  join_endpoint Nil e = SOME Nil ==> e = Nil
Proof
  metis_tac[join_endpoint_nil,join_endpoint_sym]
QED

Theorem join_network_nilSOME[simp]:
  (join_network n NNil = SOME n' ⇔ n = NNil ∧ n' = NNil) ∧
  (join_network NNil n = SOME n' ⇔ n = NNil ∧ n' = NNil)
Proof
  Cases_on ‘n’ >> simp[join_network_def, EQ_SYM_EQ]
QED

Theorem join_network_nil:
  join_network n NNil = SOME NNil ==> n = NNil
Proof
  simp[]
QED

Theorem join_network_nilNONE[simp]:
  (join_network n NNil = NONE ⇔ n ≠ NNil) ∧
  (join_network NNil n = NONE ⇔ n ≠ NNil)
Proof
  Cases_on ‘n’ >> simp[join_network_def]
QED

Theorem join_endpoint_idem[simp]:
  join_endpoint e e = SOME e
Proof
  Induct_on `e` >> rw[join_endpoint_def]
QED

Theorem join_endpoint_nil_eq_nil_right:
  !e1 e2. join_endpoint e1 Nil = SOME e2 ==> e1 = Nil /\ e2 = Nil
Proof
  simp[]
QED

Theorem join_endpoint_nil_eq_nil_left:
  !e1 e2. join_endpoint Nil e1 = SOME e2 ==> e1 = Nil /\ e2 = Nil
Proof
  simp[]
QED

Theorem join_endpoint_trans:
  !e1 e2 e3.
    join_endpoint e1 e2 = SOME e2 /\ join_endpoint e2 e3 = SOME e3
    ==> join_endpoint e1 e3 = SOME e3
Proof
  recInduct join_endpoint_ind \\
  rpt strip_tac \\
  rename1 `join_endpoint _ ee` \\
  Cases_on `ee` \\
  gvs[join_endpoint_def, AllCaseEqs()]
QED

Theorem join_network_trans:
  !n1 n2 n3.
    join_network n1 n2 = SOME n2 /\ join_network n2 n3 = SOME n3
    ==> join_network n1 n3 = SOME n3
Proof
  recInduct join_network_ind \\
  rpt strip_tac \\
  rename1 `join_network _ ee` \\
  Cases_on `ee` \\
  gvs[join_network_def, AllCaseEqs()] \\
  metis_tac[join_endpoint_trans]
QED

Theorem join_network_idem[simp]:
  join_network n n = SOME n
Proof
  Induct_on `n` >> rw[join_network_def,join_endpoint_idem]
QED

CoInductive prunes:
  join_network n1 n2 = SOME n2 /\
  (!n2'. (reduction n2 n2' ==> ?n1'. reduction n1 n1' /\ prunes n1' n2'))
  ==>
  prunes n1 n2
End

Theorem prunes_refl[simp]:
  prunes n1 n1
Proof
  ho_match_mp_tac(MP_CANON prunes_coind) \\
  qexists_tac `\x y. x = y` \\
  rw[join_network_def,reduction_def,join_network_idem]
QED

Theorem prunes_trans:
  prunes n1 n2 /\ prunes n2 n3 ==> prunes n1 n3
Proof
  strip_tac \\
  ho_match_mp_tac(MP_CANON prunes_coind) \\
  qexists_tac `\n1 n3. ?n2. prunes n1 n2 /\ prunes n2 n3` \\
  reverse conj_tac >- metis_tac[] \\
  rpt(pop_assum kall_tac) \\
  reverse(rpt strip_tac) >-
    (fs[] >>
     imp_res_tac prunes_cases >>
     metis_tac[]) >>
  fs[] >>
  imp_res_tac prunes_cases >>
  imp_res_tac join_network_trans
QED

Theorem prunes_strongcoind:
  ∀prunes'.
    (∀a0 a1.
        prunes' a0 a1 ⇒
        join_network a0 a1 = SOME a1 ∧
        ∀n2'.
          reduction a1 n2' ⇒
          ∃n1'. reduction a0 n1' ∧ (prunes' n1' n2' \/ prunes n1' n2')) ⇒
    ∀a0 a1. prunes' a0 a1 ⇒ prunes a0 a1
Proof
  rpt strip_tac \\
  ho_match_mp_tac(MP_CANON prunes_coind) \\
  qexists_tac `\x y. prunes x y \/ prunes' x y` \\
  rw[] \\
  metis_tac[prunes_cases]
QED

Theorem prunes_example:
  EVERY (λ(p,_). p ≠ p1) ARB.queue ==>
  prunes
    (NPar (NEndpoint p1 ARB (IntChoice F p2 Nil))
          (NEndpoint p2 ARB (ExtChoice p1 Nil (Send ARB ARB Nil))))
    (NPar (NEndpoint p1 ARB (IntChoice F p2 Nil))
          (NEndpoint p2 ARB (ExtChoice p1 (Receive ARB ARB Nil) (Send ARB ARB Nil))))
Proof
  strip_tac \\
  qmatch_goalsub_abbrev_tac `prunes a1 a2` \\
  ho_match_mp_tac(MP_CANON prunes_strongcoind) \\
  qexists_tac `\x y. (x = a1 /\ y = a2)` \\
  reverse conj_tac >- metis_tac[] \\
  rw[Abbr `a1`,Abbr `a2`] \\
  rw[join_network_def,join_endpoint_def,join_network_idem] \\
  fs[reduction_def] \\
  rpt(qhdtm_x_assum `trans` (assume_tac o PURE_ONCE_REWRITE_RULE [trans_cases]) \\
      fs[] \\ rveq) \\
  fs[] \\
  qexists_tac `
    (NPar (NEndpoint p1 ARB Nil)
                 (NEndpoint p2 <|queue := SNOC (p1,[0w]) ARB.queue|>
                    (ExtChoice p1 Nil (Send ARB ARB Nil))))` \\
  conj_tac >- metis_tac[trans_rules] \\
  qmatch_goalsub_abbrev_tac `prunes a1 a2` \\
  ho_match_mp_tac(MP_CANON prunes_strongcoind) \\
  qexists_tac `\x y. (x = a1 /\ y = a2)` \\
  reverse conj_tac >- metis_tac[] \\
  rw[Abbr `a1`,Abbr `a2`] \\
  rw[join_network_def,join_endpoint_def,join_network_idem] \\
  fs[reduction_def] \\
  rpt(qhdtm_x_assum `trans` (assume_tac o PURE_ONCE_REWRITE_RULE [trans_cases]) \\
      fs[] \\ rveq)
  >- (fs[APPEND_EQ_APPEND_MID |> CONV_RULE(LHS_CONV SYM_CONV)] \\
      rveq \\ fs[] \\
      fs[APPEND_EQ_SING |> CONV_RULE(LHS_CONV SYM_CONV)]) \\
  simp[SNOC_APPEND] \\
  qmatch_goalsub_abbrev_tac `prunes _ a1` \\
  qexists_tac `a1` \\
  rw[prunes_refl] \\
  unabbrev_all_tac \\
  match_mp_tac trans_par_r \\
  match_mp_tac trans_ext_choice_r' \\
  rw[]
QED

Theorem join_network_endpoint_LENGTH:
  !s1 s2 s3.
  join_network s1 s2 = SOME s3 ==>
  LENGTH(endpoints s1) = LENGTH(endpoints s2)
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] \\
  ho_match_mp_tac(fetch "-" "join_network_ind") \\
  rpt strip_tac \\
  fs[join_network_def,endpoints_def] \\
  rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq) \\ fs[endpoints_def]
QED

Theorem join_network_endpoint_LENGTH2:
  !s1 s2 s3.
  join_network s1 s2 = SOME s3 ==>
  LENGTH(endpoints s2) = LENGTH(endpoints s3)
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] \\
  ho_match_mp_tac(fetch "-" "join_network_ind") \\
  rpt strip_tac \\
  fs[join_network_def,endpoints_def] \\
  rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq) \\ fs[endpoints_def] \\
  rveq \\ fs[endpoints_def]
QED

(* TODO: move*)

Theorem MAP3_APPEND:
  !f l1 l2 l3 l1' l2' l3'.
  LENGTH l1 = LENGTH l2 /\ LENGTH l1 = LENGTH l3 ==>
  MAP3 f (l1 ++ l1') (l2 ++ l2') (l3 ++ l3') =
  MAP3 f l1 l2 l3 ++ MAP3 f l1' l2' l3'
Proof
  recInduct MAP3_ind \\
  rw[MAP3_def] \\ fs[]
QED

Theorem join_network_endpoints:
  !s1 s2 s3.
  join_network s1 s2 = SOME s3 ==>
  endpoints s3 =
  MAP2 (\e1 e2. (FST e1, FST(SND e1), THE(join_endpoint(SND(SND e1)) (SND(SND e2)))))
  (endpoints s1) (endpoints s2)
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] \\
  recInduct(fetch "-" "join_network_ind") \\
  rpt strip_tac \\
  fs[join_network_def] \\
  rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq) \\
  fs[endpoints_def] \\ rveq \\ fs[endpoints_def,join_endpoint_idem] \\
  MAP_EVERY imp_res_tac [join_network_endpoint_LENGTH,join_network_endpoint_LENGTH2] \\
  metis_tac[APPEND_LENGTH_EQ,MAP2_APPEND]
QED

Theorem prunes_endpoints:
  !s1 s2 s3.
  prunes s1 s2 ==>
  MAP FST (endpoints s1) = MAP FST (endpoints s2)
  /\
  MAP (FST o SND) (endpoints s1) = MAP (FST o SND) (endpoints s2)
Proof
  rw[Once prunes_cases] \\
  imp_res_tac join_network_endpoints \\
  imp_res_tac join_network_endpoint_LENGTH \\
  fs[MAP2_MAP] \\
  qpat_x_assum `endpoints _ = MAP _ _` (fn thm => PURE_ONCE_REWRITE_TAC [thm]) \\
  rw[MAP_MAP_o,ELIM_UNCURRY,o_DEF] \\
  simp[GSYM o_DEF] \\ metis_tac[o_ASSOC,MAP_ZIP]
QED

(* Makes sure a network has every message queue empty (epn version) *)
Definition empty_q_def:
  empty_q  NNil = T
∧ empty_q (NPar n1 n2)     = (empty_q n1 ∧ empty_q n2)
∧ empty_q (NEndpoint _ s _) = (s.queue = [])
End

(* If all queues are empty a network is only queue congruent (qcong)
   with itself (epn version)
*)
Theorem empty_queue_qcong:
  ∀epn epn'.
   qcong epn epn' ∧
   empty_q epn
   ⇒ epn' = epn
Proof
  Induct
  \\ ONCE_REWRITE_TAC [qcong_cases] \\ rw [empty_q_def]
  >- (metis_tac [qcong_rules,qcong_nil_rel_nil])
  >- (metis_tac [qcong_rules,qcong_nil_rel_nil])
  >- (drule qcong_par_rel_par_sym \\ rw []
      \\ imp_res_tac qcong_sym
      \\ fs [])
  >- (drule_then drule qcong_trans
      \\ disch_then (mp_then Any mp_tac qcong_par_rel_par)
      \\ rw [])
  >- (drule qcong_sym
      \\ disch_then (mp_then Any mp_tac qcong_endpoint_rel_endpoint)
      \\ rw [] \\ drule qcong_IMP_qrel
      \\ rw [] \\ drule qrel_LENGTH \\ rw []
      \\ rw [state_component_equality]
      \\ drule qcong_bindings_eq \\ fs [])
  >- (drule_then drule qcong_trans
      \\ disch_then (mp_then Any mp_tac qcong_endpoint_rel_endpoint)
      \\ rw [] \\ drule_then drule qcong_trans
      \\ rw [] \\ drule qcong_IMP_qrel
      \\ rw [] \\ drule qrel_LENGTH \\ rw []
      \\ rw [state_component_equality]
      \\ drule qcong_bindings_eq \\ fs [])
  \\ fs []
QED

(* If a network is empty_q it can only be junkcong with
   other empty_q networks *)
Theorem empty_q_junkcong:
  ∀epn fv epn'. junkcong fv epn epn' ∧ empty_q epn
  ⇒ empty_q epn'
Proof
  Induct
  \\ ONCE_REWRITE_TAC [junkcong_cases]
  \\ rw [empty_q_def]
  \\ rw [empty_q_def]
  >- metis_tac[empty_q_def,junkcong_nil_rel_nil,junkcong_sym]
  >- metis_tac[empty_q_def,junkcong_nil_rel_nil,junkcong_sym]
  >- (drule junkcong_sym
      \\ disch_then (mp_then Any mp_tac junkcong_par_rel_par)
      \\ rw [] \\ fs [empty_q_def] \\ metis_tac [])
  >- (drule_then drule junkcong_trans
      \\ disch_then (mp_then Any mp_tac junkcong_par_rel_par)
      \\ rw [] \\ fs [empty_q_def] \\ metis_tac [])
  >- metis_tac []
  >- metis_tac []
  >- (drule junkcong_sym
      \\ disch_then (mp_then Any mp_tac junkcong_endpoint_rel_endpoint)
      \\ rw [] \\ rw [empty_q_def]
      \\ drule junkcong_endpoint_queue_eq \\ fs [])
  \\ drule_then (drule_then assume_tac) junkcong_trans
  \\ drule junkcong_endpoint_rel_endpoint
  \\ rw [] \\ rw [empty_q_def]
  \\ drule junkcong_endpoint_queue_eq \\ fs []
QED

Theorem junkcong_net_end:
  ∀fv n1 n2. junkcong fv n1 n2 ⇒ (net_end n1 ⇔ net_end n2)
Proof
  ho_match_mp_tac junkcong_ind
  \\ rw [endpointLangTheory.net_end_def]
  \\ Cases_on ‘e’
  \\ rw [endpointLangTheory.net_end_def]
QED

val _ = export_theory ()
