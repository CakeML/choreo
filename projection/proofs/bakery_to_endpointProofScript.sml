open preamble endpointLangTheory bakery_to_endpointTheory
              endpointSemanticsTheory endpointPropsTheory
              semBakeryTheory;

val _ = new_theory "bakery_to_endpointProof";

val RTC_TRANS = save_thm ("RTC_TRANS",
  RTC_RULES |> CONV_RULE FORALL_AND_CONV |> CONJUNCTS |> el 2);

val trans_dequeue_gen = Q.store_thm("trans_dequeue_gen",
  `∀d s s' v p1 p2 e q1 q2.
    s.queue = q1 ⧺ [(p1,d)] ⧺ q2
    ∧ p1 ≠ p2 ∧ EVERY (λ(p,_). p ≠ p1) q1
    ∧ s' = s with <|queue := q1 ⧺ q2; bindings := s.bindings |+ (v,d)|>
    ⇒ trans (NEndpoint p2 s (Receive p1 v e))
            LTau
            (NEndpoint p2 s' e)`,
  rw [] >> drule trans_dequeue >> rw []
);

val trans_enqueue_choice_gen = Q.store_thm("trans_enqueue_choice_gen",
  `∀s p1 p2 e s' b.
    p1 ≠ p2
    ∧ s' = s with queue := SNOC (p1,if b then [1w] else [0w]) s.queue
    ⇒ trans (NEndpoint p2 s e)
            (LExtChoice p1 b p2)
            (NEndpoint p2 s' e)`,
  rw []
  >- (drule trans_enqueue_choice_l >> rw [])
  >- (drule trans_enqueue_choice_r >> rw [])
);

val trans_ext_choice_l_gen = Q.store_thm("trans_ext_choice_l_gen",
  `∀s s' p1 p2 e1 e2 q1 q2.
    s' = s with queue := q1 ++ q2
    ∧ s.queue = q1 ++ [(p1,[1w])] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1
    ⇒ trans (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 s' e1)`,
  rw [trans_ext_choice_l]
);

val trans_ext_choice_r_gen = Q.store_thm("trans_ext_choice_r_gen",
  `∀s s' d p1 p2 e1 e2 q1 q2.
    s' = s with queue := q1 ++ q2
    ∧ s.queue = q1 ++ [(p1,d)] ++ q2
    ∧ d ≠ [1w]
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1
    ⇒ trans (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 s' e2)`,
  rw [trans_ext_choice_r]
);

val trans_let_gen = Q.store_thm("trans_let_gen",
  `∀s s' v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ∧ s' = (s with bindings := s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl)))
    ⇒ trans (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p s' e)`,
  rw [endpointSemanticsTheory.trans_let]
);

val compile_network_preservation = Q.store_thm("compile_network_preservation",
  `∀s c α τ s' c'. trans (s,c) (α,τ) (s',c')
    ⇒ ∃s'' c''. trans_s (s',c') (s'',c'')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'' c'' (procsOf c))`,
  ho_match_mp_tac trans_pairind
  \\ rw [  compile_network_gen_def
        , procsOf_def
        , procsOf_all_distinct
        , nub'_def
        , reduction_def
        , project_def
        , FILTER_FILTER
        , FOLDL
        , fupdate_projectS]
  \\ cheat
);

val _ = export_theory ()
