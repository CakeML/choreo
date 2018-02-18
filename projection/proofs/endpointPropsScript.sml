open preamble endpointSemanticsTheory endpointLangTheory;

val _ = new_theory "endpointProps"

(* todo: lemmas that have nothing to do with endpointLang, move? *)
val RTC_SANDWICH = Q.store_thm("RTC_SANDWICH",
  `!R a b c d. R^* a b /\ R b c /\ R^* c d ==> R^* a d`,
  metis_tac[RTC_RTC,RTC_SINGLE])

val INDEX_FIND_normalize = Q.store_thm("INDEX_FIND_normalize",
  `!l n. OPTION_MAP SND (INDEX_FIND n f l) = OPTION_MAP SND (INDEX_FIND 0 f l)`,
  Induct_on `l` >> rpt strip_tac >> rw[INDEX_FIND_def]);

val INDEX_FIND_normalize' = Q.store_thm("INDEX_FIND_normalize'",
  `!l n. (INDEX_FIND n f l = NONE) = (INDEX_FIND 0 f l = NONE)`,
  Induct_on `l` >> rpt strip_tac >> rw[INDEX_FIND_def]);

val INDEX_FIND_normalize'' = Q.store_thm("INDEX_FIND_normalize''",
  `!n f l z. (INDEX_FIND (SUC n) f l = SOME z) = (FST z > 0 /\ INDEX_FIND n f l = SOME (FST z - 1, SND z))`,
  Induct_on `l` >> rpt strip_tac
  >> rw[INDEX_FIND_def,EQ_IMP_THM]
  >> fs[] >> Cases_on `z` >> fs[]);

val FIND_APPEND = Q.store_thm("FIND_APPEND",
  `FIND f (l1 ++ l2) =
   case FIND f l1 of NONE => FIND f l2
      | SOME e => SOME e`,
  Induct_on `l1` >> fs[FIND_def,INDEX_FIND_def]
  >> rw[INDEX_FIND_normalize]);

val FIND_NOT_MEM = Q.store_thm("FIND_NOT_MEM",
  `!e l. FIND ($= e) l = NONE <=> ¬MEM e l`,
  Induct_on `l` >> rw[FIND_def,INDEX_FIND_def] >> fs[FIND_def,INDEX_FIND_normalize']);

val FIND_o_NOT_MEM = Q.store_thm("FIND_o_NOT_MEM",
  `!e f l. FIND ($= e o f) l = NONE <=> ¬MEM e (MAP f l)`,
  Induct_on `l` >> rw[FIND_def,INDEX_FIND_def] >> fs[FIND_def,INDEX_FIND_normalize']);

val FIND_o_MEM = Q.store_thm("FIND_o_MEM",
  `!e f l. FIND ($= e o f) l <> NONE <=> MEM e (MAP f l)`,
  Induct_on `l` >> rw[FIND_def,INDEX_FIND_def] >> fs[FIND_def,INDEX_FIND_normalize']);

val FIND_MEM = Q.store_thm("FIND_MEM",
  `!f l z. FIND f l = SOME z
   ==> MEM z l /\ f z`,
  Induct_on `l` >> rpt strip_tac
  >> fs[FIND_def,INDEX_FIND_def] >> every_case_tac
  >> rveq >> fs[INDEX_FIND_normalize'' |> Q.SPEC `0` |> REWRITE_RULE [GSYM ONE]]
  >> metis_tac[FST,SND]);

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
  >> simp[endpointSemanticsTheory.reduction_def,trans_nil_false]);

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
     (qpat_x_assum `trans _ _ _` (assume_tac
                                    o REWRITE_RULE [Once endpointSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with bindings := a2.bindings |+ (v,d)) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS endpointSemanticsTheory.trans_rules)
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
     )
  >- (* junkcong_add_junk, symmetric case *)
     (PURE_ONCE_REWRITE_TAC [junkcong_sym_eq]
      >> qpat_x_assum `trans _ _ _` (assume_tac
                                       o REWRITE_RULE [Once endpointSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with bindings := _) a3)`
             >> qexists_tac `NEndpoint a1 a2 a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS endpointSemanticsTheory.trans_rules)
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
                 >> metis_tac[junkcong_rules,junkcong_add_junk'])))
  >- (* par-l *)
     (qpat_x_assum `trans (NPar _ _) _ _` (assume_tac
                                    o REWRITE_RULE [Once endpointSemanticsTheory.trans_cases])
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
                                    o REWRITE_RULE [Once endpointSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_com_choice_l
      >> imp_res_tac trans_com_choice_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[junkcong_rules]));

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

val junkcong_endpoints = Q.store_thm("junkcong_endpoints",
  `!fvs n1 n2. junkcong fvs n1 n2 ==> MAP FST (endpoints n1) = MAP FST (endpoints n2)`,
  ho_match_mp_tac junkcong_ind
  >> rpt strip_tac >> fs[endpoints_def]);

val junkcong_trans_pres = Q.store_thm("junkcong_trans_pres",
  `∀p1 q1 fv alpha p2.
     junkcong fv p1 q1 ∧ trans p1 alpha p2
     ⇒ ∃q2. trans q1 alpha q2 ∧ junkcong fv p2 q2`,
  metis_tac[junkcong_trans_eq])
                                     
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
  >> fs[list_trans_def] >> metis_tac[endpointSemanticsTheory.trans_par_l]);

val list_trans_par_r = Q.store_thm("list_trans_par_r",
  `∀conf p alpha q r. list_trans p alpha q ==> list_trans (NPar r p) alpha (NPar r q)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[endpointSemanticsTheory.trans_par_r]);

val endpoint_names_trans = Q.store_thm("endpoint_names_trans",
  `!n1 alpha n2. trans n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  ho_match_mp_tac trans_strongind >> rpt strip_tac >> fs[endpoints_def]);

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
  >> fs[var_names_network_def,var_names_endpoint_def]);

val partners_endpoint_def = Define `
   (partners_endpoint Nil = [])
∧ (partners_endpoint (Send p v e) = p::(partners_endpoint e))
∧ (partners_endpoint (Receive p v e) = p::(partners_endpoint e))
∧ (partners_endpoint (IntChoice b p e) =
    p::(partners_endpoint e))
∧ (partners_endpoint (ExtChoice p e1 e2) =
    p::((partners_endpoint e1) ++ (partners_endpoint e2)))
∧ (partners_endpoint (IfThen v e1 e2) = (partners_endpoint e1) ++ (partners_endpoint e2))
∧ (partners_endpoint (Let v f vl e) = partners_endpoint e)`

val partners_network_def = Define `
   (partners_network NNil = [])
∧ (partners_network (NPar n1 n2) = (partners_network n1 ++ partners_network n2))
∧ (partners_network (NEndpoint p s e) = (partners_endpoint e))`

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

enval closed_under_receiver_mem = Q.store_thm("closed_under_receiver_mem",
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
  >> fs[endpoints_def,closed_under_def,partners_endpoint_def,partners_network_def]);

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
  >> fs[endpoints_def,endpoint_ok_def,partners_endpoint_def]);

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
  >> rpt strip_tac >> fs[closed_under_def,partners_network_def,partners_endpoint_def]);

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

val _ = export_theory ()
