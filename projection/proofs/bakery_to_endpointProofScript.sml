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
  (* Com *)
  >- (MAP_EVERY Q.EXISTS_TAC [`s |+ ((v2,p2),d)`,`c'`]
     \\ IMP_RES_TAC lookup_projectS
     \\ rw [trans_s_def,fupdate_projectS]
     \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                               , `s'   = s |+ ((v2,p2),d)`
                               , `s1   = projectS p1 s`
                               , `s2   = projectS p2 s`
                               , `s2'  = projectS p2 s'`
                               , `cp1  = SND (project p1 c')`
                               , `cp2  = SND (project p2 c')`
                               , `ns   = compile_network s' c' l`
                               , `s1q  = <|bindings := s1; queue := []|>`
                               , `s2q  = <|bindings := s2; queue := []|>`
                               ]
     \\ `compile_network s (Com p1 v1 p2 v2 c') l = ns`
        by (rw [Abbr `l`, Abbr `ns`, Abbr `s'`
               , MEM_FILTER, cn_ignore_com, cn_ignore_state_update])
     \\ ASM_REWRITE_TAC []
     \\ pop_assum (K ALL_TAC)
     \\ ho_match_mp_tac RTC_TRANS
     \\ Q.EXISTS_TAC
        `NPar  (NEndpoint p1 s1q cp1)
        (NPar  (NEndpoint p2 (s2q with queue := SNOC (p1,d) s2q.queue)
                             (Receive p1 v2 cp2)) ns)`
     \\ rw [reduction_def]
     >- (ho_match_mp_tac trans_com_l
        \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`d`]
        \\ rw []
        >- (ho_match_mp_tac trans_send
           \\ rw [Abbr `s1q`])
        >- (ho_match_mp_tac trans_par_l
           \\ ho_match_mp_tac trans_enqueue
           \\ rw []))
     >- (ho_match_mp_tac RTC_SINGLE
        \\ rw [reduction_def]
        \\ ho_match_mp_tac trans_par_r
        \\ ho_match_mp_tac trans_par_l
        \\ ho_match_mp_tac trans_dequeue_gen
        \\ MAP_EVERY Q.EXISTS_TAC [`d`,`[]`,`[]`]
        \\ rw [Abbr `s2q`, Abbr `s2`,Abbr `s'`,Abbr `s2'`,projectS_fupdate]))
  (* Sel-T *)
  >- (MAP_EVERY Q.EXISTS_TAC [`s`,`c'`]
      \\ rw [trans_s_def]
      \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                                , `s1   = <| bindings := projectS p1 s;
                                             queue := [] |>`
                                , `s2   = <| bindings := projectS p2 s;
                                             queue := [] |>`
                                , `cp1  = SND (project p1 c')`
                                , `cp2  = SND (project p2 c')`
                                , `ns   = compile_network s c' l`
                                ]
      \\ `compile_network s (Sel p1 T p2 c') l = ns`
         by (rw [Abbr `l`, Abbr `ns`, MEM_FILTER, cn_ignore_sel])
      \\ ASM_REWRITE_TAC []
      \\ pop_assum (K ALL_TAC)
      \\ ho_match_mp_tac RTC_TRANS
      \\ Q.EXISTS_TAC `NPar (NEndpoint p1 s1 cp1)
                            (NPar (NEndpoint p2 (s2 with <|queue := [(p1,[1w])]|>)
                                             (ExtChoice p1 cp2 Nil))
                                  ns)`
      \\ rw []
      >- (rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_com_choice_l
         \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`T`]
         \\ rw []
         >- (ho_match_mp_tac trans_int_choice >> rw [])
         >- (ho_match_mp_tac trans_par_l
            \\ ho_match_mp_tac trans_enqueue_choice_gen
            \\ rw []))
      >- (ho_match_mp_tac RTC_SINGLE
         \\ rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_par_r
         \\ ho_match_mp_tac trans_par_l
         \\ ho_match_mp_tac trans_ext_choice_l_gen
         \\ rw []))
  (* Sel-F *)
  >- (MAP_EVERY Q.EXISTS_TAC [`s`,`c'`]
      \\ rw [trans_s_def]
      \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                                , `s1   = <| bindings := projectS p1 s;
                                             queue := [] |>`
                                , `s2   = <| bindings := projectS p2 s;
                                             queue := [] |>`
                                , `cp1  = SND (project p1 c')`
                                , `cp2  = SND (project p2 c')`
                                , `ns   = compile_network s c' l`
                                ]
      \\ `compile_network s (Sel p1 F p2 c') l = ns`
         by (rw [Abbr `l`, Abbr `ns`, MEM_FILTER, cn_ignore_sel])
      \\ ASM_REWRITE_TAC []
      \\ pop_assum (K ALL_TAC)
      \\ ho_match_mp_tac RTC_TRANS
      \\ Q.EXISTS_TAC `NPar (NEndpoint p1 s1 cp1)
                            (NPar (NEndpoint p2 (s2 with <|queue := [(p1,[0w])]|>)
                                             (ExtChoice p1 Nil cp2))
                                  ns)`
      \\ rw []
      >- (rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_com_choice_l
         \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`F`]
         \\ rw []
         >- (ho_match_mp_tac trans_int_choice >> rw [])
         >- (ho_match_mp_tac trans_par_l
            \\ ho_match_mp_tac trans_enqueue_choice_gen
            \\ rw []))
      >- (ho_match_mp_tac RTC_SINGLE
         \\ rw [reduction_def,Abbr `s1`,Abbr `s2`]
         \\ ho_match_mp_tac trans_par_r
         \\ ho_match_mp_tac trans_par_l
         \\ ho_match_mp_tac trans_ext_choice_r_gen
         \\ rw []))
  (* Let *)
  >- (MAP_EVERY Q.EXISTS_TAC [`s |+ ((v,p),f (MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl)))`,`c'`]
     \\ rw [trans_s_def]
     \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p ≠ y) (nub' (procsOf c'))`
                               , `s' = s |+ ((v,p),f (MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl)))`
                               , `s1   = projectS p s`
                               , `s1'  = projectS p s'`
                               , `cp1  = project p c'`
                               , `cp2  = project p c'`
                               , `ns   = compile_network s' c' l`
                               , `sq  = <|bindings := s1; queue := []|>`
                               , `sq'  = <|bindings := s1'; queue := []|>`
                               ]
     \\ `compile_network s (Let v p f vl c') l = ns`
        by (rw [ Abbr `l`, Abbr `ns`, Abbr `s'`, MEM_FILTER
               , cn_ignore_let , cn_ignore_state_update])
     \\ ASM_REWRITE_TAC []
     \\ pop_assum (K ALL_TAC)
     \\ ho_match_mp_tac RTC_SINGLE
     \\ rw [reduction_def]
     \\ ho_match_mp_tac trans_par_l
     \\ ho_match_mp_tac trans_let_gen
     \\ UNABBREV_ALL_TAC
     \\ rw []
     >- (Induct_on `vl` \\ rw [lookup_projectS'])
     >- (rw [projectS_fupdate] >> rpt AP_TERM_TAC
        \\ Induct_on `vl` >> rw [lookup_projectS']))
  \\ cheat
);

val _ = export_theory ()
