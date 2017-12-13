open preamble payloadSemanticsTheory payloadLangTheory;

val _ = new_theory "payloadProps"

val (qcong_rules, qcong_ind, qcong_cases) = Hol_reln `
(* Basic congruence rules *)

  (* Symmetric *)
  (∀n. qcong n n)

  (* Reflexive *)
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

val trans_enqueue' = Q.store_thm("trans_enqueue'",
  `∀conf s d p1 p2 e q.
     p1 ≠ p2
     ⇒ trans conf (NEndpoint p2 (s with queue := q) e) (LReceive p1 d p2)
       (NEndpoint p2 (s with queue := SNOC (p1,d) q) e)`,
  rpt strip_tac
  >> `s with queue := SNOC (p1,d) q = (s with queue := q) with queue := SNOC (p1,d) ((s with queue := q).queue)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue
  >> simp[]);

val trans_enqueue_choice_r' = Q.store_thm("trans_enqueue_choice_r'",
  `∀conf s p1 p2 e q.
     p1 ≠ p2 ⇒
     trans conf (NEndpoint p2 (s with queue := q) e) (LExtChoice p1 F p2)
       (NEndpoint p2 (s with queue := SNOC (p1,[6w; 0w]) q) e)`,
  rpt strip_tac
  >> `!d. s with queue := SNOC (p1,d) q = (s with queue := q) with queue := SNOC (p1,d) ((s with queue := q).queue)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue_choice_r
  >> simp[]);

val trans_enqueue_choice_l' = Q.store_thm("trans_enqueue_choice_l'",
  `∀conf s p1 p2 e q.
     p1 ≠ p2 ⇒
     trans conf (NEndpoint p2 (s with queue := q) e) (LExtChoice p1 T p2)
       (NEndpoint p2 (s with queue := SNOC (p1,[6w; 1w]) q) e)`,
  rpt strip_tac
  >> `!d. s with queue := SNOC (p1,d) q = (s with queue := q) with queue := SNOC (p1,d) ((s with queue := q).queue)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue_choice_l
  >> simp[]);

val trans_dequeue_last_payload' = Q.store_thm("trans_dequeue_last_payload'",
  `∀conf s v p1 p2 e q1 q2 d ds.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ⇒
     trans conf (NEndpoint p2 (s with queue := q1 ⧺ [(p1,6w::d)] ⧺ q2) (Receive p1 v ds e)) LTau
       (NEndpoint p2
          <|bindings := s.bindings |+ (v,FLAT (SNOC d ds));
            queue := q1 ⧺ q2|> e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s.bindings = (s with queue := a1).bindings` by simp[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac (trans_dequeue_last_payload |> SIMP_RULE (srw_ss()) [])
  >> simp[]);

val trans_dequeue_intermediate_payload' = Q.store_thm("trans_dequeue_intermediate_payload'",
  `∀conf s v p1 p2 e q1 q2 d ds.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ⇒
     trans conf (NEndpoint p2 (s with queue := q1 ⧺ [(p1,2w::d)] ⧺ q2) (Receive p1 v ds e)) LTau
       (NEndpoint p2 (s with queue := q1 ⧺ q2)
          (Receive p1 v (SNOC d ds) e))`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s with queue := q1 ++ q2 = ((s with queue := a1) with queue := q1 ++ q2)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac (trans_dequeue_intermediate_payload)
  >> simp[]);

val trans_ext_choice_l' = Q.store_thm("trans_ext_choice_l'",
  `∀conf s p1 p2 e1 e2 q1 q2.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ⇒
     trans conf (NEndpoint p2 (s with queue := q1 ⧺ [(p1,[6w; 1w])] ⧺ q2) (ExtChoice p1 e1 e2)) LTau
       (NEndpoint p2 (s with queue := q1 ⧺ q2) e1)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s with queue := q1 ++ q2 = ((s with queue := a1) with queue := q1 ++ q2)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac (trans_ext_choice_l)
  >> simp[]);

val trans_ext_choice_r' = Q.store_thm("trans_ext_choice_r'",
  `∀conf s p1 p2 e1 e2 q1 q2.
     p1 ≠ p2 ∧
     EVERY (λ(p,_). p ≠ p1) q1 ⇒
     trans conf (NEndpoint p2 (s with queue := q1 ⧺ [(p1,[6w; 0w])] ⧺ q2) (ExtChoice p1 e1 e2)) LTau
       (NEndpoint p2 (s with queue := q1 ⧺ q2) e2)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `_ with queue := a1`
  >> `s with queue := q1 ++ q2 = ((s with queue := a1) with queue := q1 ++ q2)` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac (trans_ext_choice_r)
  >> simp[]);

val qcong_trans_eq = Q.store_thm("qcong_trans_eq",
  `∀p1 q1 .
     qcong p1 q1
     ⇒ ∀ conf alpha p2 q2.
            ((trans conf p1 alpha p2 ⇒ (∃q2. trans conf q1 alpha q2 ∧ qcong p2 q2))
         ∧ (trans conf q1 alpha q2 ⇒ (∃p2. trans conf p1 alpha p2 ∧ qcong p2 q2)))`,
  ho_match_mp_tac qcong_strongind
  >> rpt strip_tac
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- metis_tac[qcong_rules]
  >- (qpat_x_assum `trans _ _ _ _` (assume_tac
                                       o REWRITE_RULE [Once payloadSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := q1 ⧺ [(p2,d2); (p1,d1)] ⧺ q2) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS payloadSemanticsTheory.trans_rules)
                 >> fs[])
             >- metis_tac[qcong_rules])
      >> TRY(qmatch_goalsub_abbrev_tac `qcong (NEndpoint a1 (a2 with queue := SNOC a3 _) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with queue := SNOC a3 (q1 ++ [(p2,d2);(p1,d1)] ++ q2)) a4`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac [trans_enqueue',
                                            trans_enqueue_choice_l',
                                            trans_enqueue_choice_r']
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
      >> TRY(fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[Once APPEND_EQ_CONS]
             >> fs[APPEND_EQ_SING] >> rveq >> fs[] >> rveq >> fs[]
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ a4 ++ [a5;a6] ++ a7|>) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ a4 ++ [a6;a5] ++ a7|>) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> SIMP_TAC bool_ss [GSYM APPEND_ASSOC]
                        >> SIMP_TAC bool_ss [Once APPEND_ASSOC]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder''])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 l2. l1 ++ [e1] ++ l2 = l1 ++ (e1::l2)`,
                                    simp[])]
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = l1 ++ [e1] ++ (e2::l2)`,
                                    simp[])]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4] ++ a5|>) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = (l1 ++ [e1]) ++ [e2] ++ l2`,
                                    simp[])]
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a4;a5] ++ a6 ++ a7|>) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (<|bindings := a2 ; queue := a3 ++ [a5;a4] ++ a6 ++ a7|>) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> match_mp_tac trans_dequeue_last_payload'
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder'',APPEND_ASSOC])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ a4 ++ [a5;a6] ++ a7) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ a4 ++ [a6;a5] ++ a7) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> SIMP_TAC bool_ss [GSYM APPEND_ASSOC]
                        >> SIMP_TAC bool_ss [Once APPEND_ASSOC]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload',
                                      trans_ext_choice_l',
                                      trans_ext_choice_r']
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder'])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 l2. l1 ++ [e1] ++ l2 = l1 ++ (e1::l2)`,
                                    simp[])]
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = l1 ++ [e1] ++ (e2::l2)`,
                                    simp[])]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload',
                                      trans_ext_choice_l',
                                      trans_ext_choice_r']
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a4] ++ a5) a6`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> PURE_ONCE_REWRITE_TAC
                           [Q.prove(`!l1 e1 e2 l2. l1 ++ [e1;e2] ++ l2 = (l1 ++ [e1]) ++ [e2] ++ l2`,
                                    simp[])]
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload',
                                      trans_ext_choice_l',
                                      trans_ext_choice_r']
                        >> simp[])
                    >> metis_tac[qcong_refl])
             >> TRY(qmatch_goalsub_abbrev_tac
                      `qcong (NEndpoint a1 (a2 with queue := a3 ++ [a4;a5] ++ a6 ++ a7) a8)`
                    >> qexists_tac
                       `NEndpoint a1 (a2 with queue := a3 ++ [a5;a4] ++ a6 ++ a7) a8`
                    >> conj_tac
                    >- (unabbrev_all_tac
                        >> MAP_FIRST match_mp_tac
                                     [trans_dequeue_intermediate_payload',
                                      trans_ext_choice_l',
                                      trans_ext_choice_r']
                        >> simp[])
                    >> metis_tac[qcong_queue_reorder',APPEND_ASSOC])))
  >- cheat
  >- (qpat_x_assum `trans _ _ _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemanticsTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_com_choice_l
      >> imp_res_tac trans_com_choice_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[qcong_rules])
  >- (qpat_x_assum `trans _ _ _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemanticsTheory.trans_cases])
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
  `∀p1 q1 conf alpha p2.
     qcong p1 q1 ∧ trans conf p1 alpha p2
     ⇒ ∃q2. trans conf q1 alpha q2 ∧ qcong p2 q2`,
  metis_tac[qcong_trans_eq])

val _ = export_theory ()
