open preamble choreoUtilsTheory
              endpointLangTheory chor_to_endpointTheory
              endpointSemTheory endpointPropsTheory
              endpointCongTheory chorSemTheory chorPropsTheory
              endpointConfluenceTheory chorConfluenceTheory
              chorSyncPropsTheory;

val _ = new_theory "chor_to_endpointProof";

val _ = set_grammar_ancestry
  ["endpointProps","endpointLang","endpointConfluence",
   "chor_to_endpointProof","chorSem","chorLang"];

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
  rw [endpointSemTheory.trans_let]
);

val cut_sel_upto_def = Define`
  cut_sel_upto p (Sel p1 b p2 c) =
    (if p = p1 then
       cut_sel_upto p c
     else
       Sel p1 b p2 c)
∧ cut_sel_upto p c = c
`;

val compile_network_eq_all_project = Q.store_thm("compile_network_eq_all_project",
  `∀c c' s l. compile_network_ok s c l
    ∧ (∀p. MEM p l ⇒ project' p c = project' p c')
    ⇒ compile_network s c l = compile_network s c' l`,
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
);

val compile_network_ok_project_ok = Q.store_thm("compile_network_ok_project_ok",
  `∀s c l p.
    compile_network_ok s c l
    ∧ MEM p l
    ⇒ project_ok p c`,
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
);

val compile_network_ok_dest_sel = Q.store_thm("compile_network_ok_dest_sel",
  `∀s c l p b q.
    compile_network_ok s (Sel p b q c) l
    ⇒ compile_network_ok s c l`,
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
);

Theorem compile_network_ok_dest_sel':
  ∀s c l p b q.
    compile_network_ok s (Sel p b q c) l
    ⇒ (p <> q \/ (~MEM p l /\ ~MEM q l))
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
QED

Theorem compile_network_ok_selI:
  ∀s c l p b q.
    compile_network_ok s c l /\ (p <> q \/ (~MEM p l /\ ~MEM q l))
    ⇒ compile_network_ok s (Sel p b q c) l
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac[]
QED

Theorem compile_network_ok_dest_com:
  ∀s p1 v1 p2 v2 c l.
    compile_network_ok s (Com p1 v1 p2 v2 c) l
    ⇒ compile_network_ok (s |+ ((v2,p2),d)) c l
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
QED

Theorem compile_network_ok_dest_com_asynch:
  ∀s p1 v1 p2 v2 c l.
    compile_network_ok s (Com p1 v1 p2 v2 c) l
    ⇒ compile_network_ok s c l
Proof
  Induct_on `l`
  \\ rw [compile_network_gen_def,project_def]
  \\ metis_tac []
QED

val project_if_l_eq = Q.store_thm("project_if_l_eq",
  `∀v p q c1 c2.
    project_ok q (IfThen v p c1 c2)
    ∧ p ≠ q
    ∧ (∀b t c'. c1 ≠ Sel p b t c')
    ⇒ project' q (IfThen v p c1 c2) = project' q c1`,
  Cases_on `c1`
  \\ rw [project_def,cut_sel_upto_def,split_sel_def]
  \\ fs [project_def,cut_sel_upto_def,split_sel_def]
  \\ TRY (qpat_x_assum `(_,_) = project _ _` (ASSUME_TAC o GSYM))
  \\ rfs []
  \\ fs []
  \\ TRY (qpat_x_assum `(_,_) = project _ _` (ASSUME_TAC o GSYM))
  \\ every_case_tac
  \\ rw []
);

val project_if_r_eq = Q.store_thm("project_if_r_eq",
  `∀v p q c1 c2.
    project_ok q (IfThen v p c1 c2)
    ∧ p ≠ q
    ∧ (∀b t c'. c2 ≠ Sel p b t c')
    ⇒ project' q (IfThen v p c1 c2) = project' q c2`,
  Cases_on `c2`
  \\ rw [project_def,cut_sel_upto_def,split_sel_def]
  \\ fs [project_def,cut_sel_upto_def,split_sel_def]
  \\ TRY (qpat_x_assum `(_,_) = project _ _` (ASSUME_TAC o GSYM))
  \\ rfs []
  \\ fs []
  \\ TRY (qpat_x_assum `(_,_) = project _ _` (ASSUME_TAC o GSYM))
  \\ every_case_tac
  \\ rw []
);

val compile_network_if_l_eq = Q.store_thm("compile_network_if_l_eq",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ∧ ¬MEM p l
    ∧ (∀b q c'. c1 ≠ Sel p b q c')
    ⇒ compile_network s (IfThen v p c1 c2) l = compile_network s c1 l`,
  rw []
  \\ ho_match_mp_tac compile_network_eq_all_project
  \\ rw []
  \\ imp_res_tac compile_network_ok_project_ok
  \\ ho_match_mp_tac project_if_l_eq
  \\ rw []
  \\ Cases_on `p = p'`
  \\ fs []
);

val split_sel_project_ok = Q.store_thm("split_sel_project_ok",
  `!h p c b r. h <> p /\ split_sel h p c = SOME (b,r)
   /\ project_ok h r
   ==> project_ok h c`,
  Induct_on `c` >> rw[project_def,split_sel_def]
  >> metis_tac[]);

val split_sel_project_ok2 = Q.store_thm("split_sel_project_ok2",
  `!h p c b r. h <> p /\ split_sel h p c = SOME (b,r)
   /\ project_ok h c
   ==> project_ok h r`,
  Induct_on `c` >> rw[project_def,split_sel_def]
  >> metis_tac[]);

val compile_network_if_l = Q.store_thm("compile_network_if_l",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ⇒ compile_network_ok s c1 l`,
  Induct_on `l` >> rw[compile_network_gen_def,project_def]
  >> every_case_tac >> fs[]
  >> first_x_assum drule >> strip_tac >> fs[]
  >> metis_tac[split_sel_project_ok]);

val compile_network_if_r = Q.store_thm("compile_network_if_r",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ⇒ compile_network_ok s c2 l`,
  Induct_on `l` >> rw[compile_network_gen_def,project_def]
  >> every_case_tac >> fs[]
  >> first_x_assum drule >> strip_tac >> fs[]
  >> metis_tac[split_sel_project_ok]);

val compile_network_if_r_eq = Q.store_thm("compile_network_if_r_eq",
  `∀s v p c1 c2 l.
    compile_network_ok s (IfThen v p c1 c2) l
    ∧ ¬MEM p l
    ∧ (∀b p2 c'. c2 ≠ Sel p b p2 c')
    ⇒ compile_network s (IfThen v p c1 c2) l = compile_network s c2 l`,
  rw []
  \\ ho_match_mp_tac compile_network_eq_all_project
  \\ rw []
  \\ imp_res_tac compile_network_ok_project_ok
  \\ ho_match_mp_tac project_if_r_eq
  \\ rw []
  \\ Cases_on `p = p'`
  \\ fs []
);

val FST_endpoints_compile_network = Q.store_thm("FST_endpoints_compile_network",
  `∀s c l. MAP FST (endpoints (compile_network s c l)) = l`,
  Induct_on `l`
  \\ rw [endpoints_def,compile_network_gen_def]
);

val preSel_def = Define`
  preSel p (Sel p1 b p2 c) =
    (if p1 = p
     then (b,p2)::preSel p c
     else [])
∧ preSel _ _ = []
`;

val projPre_def = Define`
  projPre p ((b,q)::l) ep = IntChoice b q (projPre p l ep)
∧ projPre p [] ep = ep
`

val prefix_project_eq = Q.store_thm("prefix_project_eq",
  `∀p c. project_ok p c
    ⇒ project' p c = projPre p (preSel p c) (project' p (cut_sel_upto p c))`,
  Induct_on `c`
  \\ rw []
  \\ TRY (Cases_on `p = s0`)
  \\ rw [project_def,preSel_def,cut_sel_upto_def,projPre_def]
  \\ fs [project_def]
);

val list_trans_projpre = Q.store_thm("list_trans_projpre",
  `!p sq c' e.
     ~MEM p (MAP SND (preSel p c'))
     ==>
     list_trans (NEndpoint p sq (projPre p (preSel p c') e))
                      (MAP (λ(b,q). LIntChoice p b q) (preSel p c'))
                      (NEndpoint p sq e)`,
  Induct_on `c'`
  >> TRY(rw[preSel_def,projPre_def,list_trans_def] \\ NO_TAC)
  >> rpt strip_tac
  >> simp[preSel_def]
  >> reverse IF_CASES_TAC
  >- rw[preSel_def,projPre_def,list_trans_def]
  >> rveq >> rename1 `NEndpoint p`
  >> simp[list_trans_def,PULL_EXISTS,projPre_def]
  >> qmatch_goalsub_abbrev_tac `IntChoice _ _ a1`
  >> qexists_tac `NEndpoint p sq a1`
  >> qunabbrev_tac `a1`
  >> qpat_x_assum `¬ _` mp_tac
  >> simp[preSel_def] >> strip_tac
  >> simp[trans_int_choice]);

(* TODO: move to endpointProps? *)
val list_trans_com_choice_l = Q.store_thm("list_trans_com_choice_l",
 `!icl ecl n1 n2 n1' n2'.
  EVERY2 (\ic ec. ?p b q. ic = LIntChoice p b q /\ ec = LExtChoice p b q) icl ecl
  /\ list_trans n1 icl n1' /\ list_trans n2 ecl n2'
  ==>
  reduction^* (NPar n1 n2) (NPar n1' n2')`,
  simp[GSYM AND_IMP_INTRO, GSYM PULL_FORALL]
  >> ho_match_mp_tac LIST_REL_ind >> rpt strip_tac
  >> fs[list_trans_def]
  >> rveq
  >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
  >> imp_res_tac sender_receiver_distinct_choice
  >> imp_res_tac trans_com_choice_l
  >> simp[reduction_def]
  >> asm_exists_tac >> simp[]);

val list_trans_com_choice_l' = Q.store_thm("list_trans_com_choice_l'",
 `!icl ecl n1 n2 n1' n2' n2''.
  EVERY2 (\ic ec. ?p b q. ic = LIntChoice p b q /\ ec = LExtChoice p b q) icl ecl
  /\ list_trans n1 icl n1' /\ list_trans n2 ecl n2'
  /\ reduction^* n2' n2''
  ==>
  reduction^* (NPar n1 n2) (NPar n1' n2'')`,
  metis_tac[reduction_par_r,RTC_RTC,list_trans_com_choice_l]);

val trans_fold_par = Q.store_thm("trans_fold_par",
  `!n1 e1 e2 n2 alpha. trans e1 alpha e2
   ==> trans (FOLDR NPar NNil (n1 ++ e1::n2)) alpha (FOLDR NPar NNil (n1 ++ e2::n2))`,
  Induct >> rw[] >> metis_tac[trans_par_l,trans_par_r]);

val trans_fold_par' = Q.store_thm("trans_fold_par'",
  `!n1 n1' e1 e2 n2 n2' alpha. trans e1 alpha e2 /\ n1 = n1' /\ n2 = n2'
   ==> trans (FOLDR NPar NNil (n1 ++ e1::n2)) alpha (FOLDR NPar NNil (n1' ++ e2::n2'))`,
  metis_tac[trans_fold_par]);

val preSel_to_queue_def = Define
  `preSel_to_queue proc1 proc2 l =
    MAP (λ(b,p). (proc2,if b then [1w] else [0w])) (FILTER ($= proc1 o SND) l)`

val compile_network_ok_if_eq = Q.store_thm("compile_network_ok_if_eq",
  `!s v p c' c2 l.
   compile_network_ok s (IfThen v p c' c2) l /\
   ~MEM p l ==>
   compile_network s (IfThen v p c' c2) l =
   FOLDR NPar NNil
   (MAP (\proc. NEndpoint proc (<| bindings := projectS proc s;
                                   queue    := [] |>) (project' proc (IfThen v p c' c2))) l)`,
   Induct_on `l`
   >- rw[compile_network_gen_def]
   >> rpt strip_tac
   >> fs[compile_network_gen_def]
   >> fs[project_def]);

val cut_ext_choice_upto_presel_def = Define `
   (cut_ext_choice_upto_presel p1 p2 presel Nil = Nil)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Send p v e) = Send p v e)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Receive p v e) = Receive p v e)
/\ (cut_ext_choice_upto_presel p1 p2 presel (IfThen b e1 e2) = IfThen b e1 e2)
/\ (cut_ext_choice_upto_presel p1 p2 presel (IntChoice p b' e) = IntChoice p b' e)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Let s f l c) = Let s f l c)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Fix s c) = Fix s c)
/\ (cut_ext_choice_upto_presel p1 p2 presel (Call s) = Call s)
/\ (cut_ext_choice_upto_presel p1 p2 presel (ExtChoice p e1 e2) =
    (if p = p1 then
      (case SPLITP ($= p2 o SND) presel of
       (_,[]) => ExtChoice p e1 e2
     | (_,(T,_)::presel) => cut_ext_choice_upto_presel p1 p2 presel e1
     | (_,(F,_)::presel) => cut_ext_choice_upto_presel p1 p2 presel e2)
     else ExtChoice p e1 e2))`

val cut_ext_choice_upto_presel_nil = Q.store_thm("cut_ext_choice_upto_presel_nil",
  `cut_ext_choice_upto_presel p1 p2 [] c = c`,
  Induct_on `c` >> rw[cut_ext_choice_upto_presel_def,SPLITP]
                                                );

val cut_ext_choice_upto_presel_cons = Q.store_thm("cut_ext_choice_upto_presel_cons",
  `p2 <> p3
   ==>
   cut_ext_choice_upto_presel p1 p2 ((b,p3)::l) c =
   cut_ext_choice_upto_presel p1 p2 l c`,
  Induct_on `c` >> rw[cut_ext_choice_upto_presel_def,SPLITP]
  >> rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq));

val project_cut_sel_eq = Q.store_thm("project_cut_sel_eq",
  `!h p c1.
   p ≠ h /\ project_ok h c1 ==>
   project' h (cut_sel_upto p c1) =
   cut_ext_choice_upto_presel p h (preSel p c1) (project' h c1)`,
  Induct_on `c1`
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >- rw[cut_sel_upto_def,cut_ext_choice_upto_presel_nil,preSel_def]
  >> rw[cut_sel_upto_def]
  >> simp[preSel_def] >> rw[cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_nil]
  >> rw[project_def,cut_ext_choice_upto_presel_def,SPLITP]
  >> simp[cut_ext_choice_upto_presel_cons]
  >> first_x_assum match_mp_tac >> fs[project_def] >> every_case_tac >> fs[]);

val FILTER_nub = Q.store_thm("FILTER_nub",
  `!P l. FILTER P (nub' l) = nub' (FILTER P l)`,
  Induct_on `l` >> rpt strip_tac
  >> fs[nub'_def] >> rw[nub'_def]
  >> first_assum(qspec_then `P`  (assume_tac o GSYM))
  >> first_x_assum(qspec_then `(λy. h ≠ y)` (assume_tac o GSYM))
  >> simp[FILTER_FILTER] >> simp[Once CONJ_SYM]
  >> rw[FILTER_EQ,EQ_IMP_THM] >> CCONTR_TAC >> fs[]);

val set_nub' = Q.store_thm("set_nub'",
  `!l. set(nub' l) = set l`,
  Induct >> rw[nub'_def] >> simp[GSYM FILTER_nub]
  >> simp[LIST_TO_SET_FILTER,INTER_DEF]
  >> rw[FUN_EQ_THM,EQ_IMP_THM] >> simp[]
  >> metis_tac[]);

val compile_network_cut_sel_upto = Q.store_thm("compile_network_cut_sel_upto",
  `!s v p c1 l.
  compile_network_ok s c1 l /\
  ~MEM p l ==>
  compile_network s (cut_sel_upto p c1) l =
  FOLDR NPar NNil
   (MAP (\proc. NEndpoint proc (<| bindings := projectS proc s;
                                   queue    := [] |>) (cut_ext_choice_upto_presel p proc (preSel p c1) (project' proc c1))) l)`,
  Induct_on `l`
  >- (rw[compile_network_gen_def])
  >> rpt strip_tac
  >> fs[compile_network_gen_def,project_def,
        split_sel_def,cut_sel_upto_def,cut_ext_choice_upto_presel_def]
  >> fs[project_cut_sel_eq]);

val MEM_presel_MEM_procsOf = Q.store_thm("MEM_presel_MEM_procsOf",
  `!c p. project_ok p c  /\ MEM p (MAP SND (preSel p c))
   ==> F`,
  Induct
  >- rw[preSel_def,project_def]
  >- rw[preSel_def,project_def]
  >- rw[preSel_def,project_def]
  >- rw[preSel_def,project_def]
  >> rpt strip_tac
  >> fs[project_def,preSel_def]
  >> rpt(PURE_FULL_CASE_TAC >> fs[]) >> metis_tac[]);

val network_consume_LExtChoice = Q.store_thm("network_consume_LExtChoice",
  `∀psl qf s c l p.
       ¬MEM p l ∧ ¬MEM p (MAP SND psl) ∧ ALL_DISTINCT l ∧
       (∀x. MEM x (MAP SND psl) ⇒ MEM x l) ⇒
       list_trans
         (FOLDR NPar NNil
            (MAP
               (λproc.
                    NEndpoint proc
                      <|bindings := projectS proc s; queue := qf proc|>
                      (project' proc c)) l))
         (MAP (λ(b,q). LExtChoice p b q) psl)
         (FOLDR NPar NNil
            (MAP
               (λproc.
                    NEndpoint proc
                      <|bindings := projectS proc s;
                      queue := qf proc ⧺ preSel_to_queue proc p psl|>
                      (project' proc c)) l))`,
  Induct
  >- (rw[list_trans_def,preSel_to_queue_def])
  \\ rw[list_trans_def]
  \\ rw[preSel_to_queue_def]
  \\ `MEM (SND h) l` by simp[]
  \\ Cases_on `h` >> simp[]
  \\ rename1 `LExtChoice p1 b p2`
  \\ qexists_tac
       `FOLDR NPar NNil
              (MAP
                (λproc.
                  NEndpoint proc
                    <|bindings := projectS proc s; queue :=
                      qf proc ++ if proc = p2 then [(p1, if b then [1w] else [0w])] else [] |>
                    (project' proc c)) l)`
  \\ conj_tac
  >- (pop_assum(strip_assume_tac o REWRITE_RULE [MEM_SPLIT])
      \\ simp[] \\ match_mp_tac trans_fold_par'
      \\ conj_tac
      >- (match_mp_tac trans_enqueue_choice_gen >> fs[])
      \\ fs[]
      \\ rw[MAP_EQ_f]
      \\ rw[] \\ fs[ALL_DISTINCT_APPEND] \\ metis_tac[])
  \\ fs[]
  \\ first_x_assum(qspec_then `\proc. qf proc ⧺
                   if proc = p2 then [(p1,if b then [1w] else [0w])] else []` mp_tac)
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ disch_then(qspecl_then [`p1`,`l`] mp_tac)
  \\ rpt(disch_then drule)
  \\ Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_FORALL]
  \\ impl_tac >- rw[]
  \\ disch_then(qspecl_then [`c`,`s`] mp_tac)
  \\ qmatch_goalsub_abbrev_tac `list_trans (FOLDR _ _ a1) _ (FOLDR _ _ a2)
                                 ==> list_trans (FOLDR _ _ a3) _ (FOLDR _ _ a4)`
  \\ `a1 = a3 /\ a2 = a4` suffices_by simp[]
  \\ unabbrev_all_tac
  \\ rw[MAP_EQ_f] \\ rw[preSel_to_queue_def]
);

val epn_conf_def = Define`
  epn_conf p q = ∃p' q'. reduction^* p p' ∧ reduction^* q q' ∧ qcong p' q'
`
val _ = Parse.add_infix("≅<",425,Parse.NONASSOC);
val _ = Parse.overload_on("≅<",``epn_conf``);

Theorem conf_refl:
  ∀epn. epn ≅< epn
Proof
  rw [epn_conf_def]
  \\ map_every qexists_tac [`epn`,`epn`]
  \\ rw [reduction_def,qcong_refl]
QED

Theorem conf_sym:
  ∀epn epn'. epn ≅< epn' ⇒ epn' ≅< epn
Proof
  metis_tac [epn_conf_def,qcong_sym]
QED

Theorem conf_distinct:
  ∀epn epn'.
   epn ≅< epn' ∧
   ALL_DISTINCT (MAP FST (endpoints epn))
   ⇒ ALL_DISTINCT (MAP FST (endpoints epn'))
Proof
  metis_tac[ qcong_endpoints
           , endpoint_names_reduction
           , epn_conf_def]
QED

Theorem projectS_fupdate_fresh:
  p <> p' ==>
  projectS p (s |+ ((v,p'),d)) = projectS p s
Proof
  rw[projectS_def]
QED

Theorem trans_not_eq:
  ∀s c τ l s' c'. trans (s,c) (τ,l) (s',c') ∧ τ ≠ LFix ⇒ c ≠ c'
Proof
  ONCE_REWRITE_TAC [GSYM AND_IMP_INTRO]
  \\ ho_match_mp_tac trans_pairind \\ rw []
  \\ disch_then (mp_tac o AP_TERM “chor_size”) \\ EVAL_TAC \\ fs []
QED

Definition catchup_of_def:
  (catchup_of (LTau p ps) c = cut_sel_upto p c) ∧
  catchup_of _ c = c
End

Theorem compile_network_ok_subset:
  ∀s c ps qs.
  compile_network_ok s c qs ∧ set ps ⊆ set qs ⇒
  compile_network_ok s c ps
Proof
  Induct_on ‘ps’ >>
  rw[compile_network_gen_def] >- imp_res_tac compile_network_ok_project_ok >>
  res_tac
QED

Theorem trans_ln_catchup_of:
  ∀p τ.
  no_self_comunication (SND p) ⇒
  trans_ln p (FST p,catchup_of τ (SND p))
Proof
  Cases_on ‘τ’ >> fs[catchup_of_def,trans_ln_refl] >>
  PairCases >> Induct_on ‘p1’ >>
  fs[cut_sel_upto_def,trans_ln_refl,no_self_comunication_def] >>
  rw[trans_ln_refl] >>
  match_mp_tac trans_ln_step >>
  rw[chor_tl_def] >>
  metis_tac[trans_sel]
QED

Theorem trans_ln_catchup_of_pair =
  Q.SPEC ‘(s,c)’ trans_ln_catchup_of  |> SIMP_RULE std_ss []  |> GEN_ALL

Theorem trans_ln_cut_sel_upto:
  ∀s c p.
  no_self_comunication c ⇒
  trans_ln (s,c) (s,cut_sel_upto p c)
Proof
  rw[] >>
  qspecl_then [‘(s,c)’,‘LTau p ARB’] assume_tac trans_ln_catchup_of >>
  fs[catchup_of_def]
QED

Theorem compile_network_ok_no_self_comunication:
  ∀s c.
  compile_network_ok s c (procsOf c) ⇒
  no_self_comunication c
Proof
  rw[] >>
  dxrule compile_network_ok_project_ok >>
  simp[Once MONO_NOT_EQ] >>
  Induct_on ‘c’ >>
  rw[project_def,no_self_comunication_def,procsOf_def,nub'_def,procsOf_all_distinct] >>
  res_tac >> fs[] >>
  rw[MEM_FILTER,MEM_nub'] >>
  rw[RIGHT_AND_OVER_OR,EXISTS_OR_THM] >-
    (Cases_on ‘s = p’ >> simp[] >>
     disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]) >-
    (Cases_on ‘s = p’ >> simp[] >>
     disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]) >-
    (Cases_on ‘s0 = p’ >> simp[] >>
     Cases_on ‘s2 = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (Cases_on ‘s = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (Cases_on ‘s0 = p’ >> simp[] >>
     Cases_on ‘s = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (Cases_on ‘s0 = p’ >> simp[] >>
     Cases_on ‘s = p’ >> simp[] >>
     rpt disj2_tac >>
     qexists_tac ‘p’ >>
     rw[] >>
     rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
     metis_tac[split_sel_project_ok,split_sel_project_ok2]
     ) >-
    (asm_exists_tac \\ simp [])
QED

Triviality dsubst_subset_procsOf:
  ∀c dn c'.
    set (procsOf (dsubst c dn c')) ⊆ set (procsOf c) ∪ set (procsOf c')
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [procsOf_def,chorLangTheory.dsubst_def,set_nub']
  \\ irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
  \\ fs [SUBSET_DEF]
QED

Triviality procsOf_subset_dsubst:
  ∀c dn c'.
    set (procsOf c) ⊆ set (procsOf (dsubst c dn c'))
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [procsOf_def,chorLangTheory.dsubst_def,set_nub']
  \\ fs [SUBSET_DEF]
QED

Theorem dsubst_procsOf_set_eq:
  ∀c dn. set (procsOf c) = set (procsOf (dsubst c dn c))
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [procsOf_subset_dsubst,
                dsubst_subset_procsOf,
                UNION_IDEMPOT]
QED

Theorem dsubst_procsOf_set_eq_Fix:
  ∀c x y. set (procsOf c) = set (procsOf (dsubst c x (Fix y c)))
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [procsOf_subset_dsubst,
                dsubst_subset_procsOf,
                procsOf_def,
                set_nub',
                UNION_IDEMPOT]
QED

Theorem procsOf_dsubst_MEM_eq:
  ∀c p x y. MEM p (procsOf c) ⇔ MEM p (procsOf (dsubst c x (Fix y c)))
Proof
  rw []
  \\ qspecl_then [‘c’,‘x’,‘y’] (assume_tac) dsubst_procsOf_set_eq_Fix
  \\ pop_assum (assume_tac o Q.AP_TERM ‘(λx. p IN x)’) \\ fs []
QED

Theorem procsOf_dsubst_MEM =
  SPEC_ALL procsOf_dsubst_MEM_eq
  |> EQ_IMP_RULE
  |> fst
  |> GEN_ALL

Theorem dsubst_procsOf_MEM =
  SPEC_ALL procsOf_dsubst_MEM_eq
  |> EQ_IMP_RULE
  |> snd
  |> GEN_ALL

Theorem compile_network_preservation_ln:
   ∀s c α s' c' . compile_network_ok s c (procsOf c)
    ∧ trans (s,c) (α,[]) (s',c') ∧ chor_tl s c = (s',c')
    ⇒ trans_ln (s',c') (s',catchup_of α c')
       ∧ reduction^* (compile_network s  c  (procsOf c))
                      (compile_network s' (catchup_of α c') (procsOf c))
Proof
    `∀s c α τ s' c'. trans (s,c) (α,τ) (s',c')
    ⇒ (compile_network_ok s c (procsOf c) ∧ τ = [] ∧ chor_tl s c = (s',c') ∧
        no_self_comunication c
    ⇒ trans_ln (s',c') (s',catchup_of α c')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'  (catchup_of α c') (procsOf c)))`
  suffices_by metis_tac [compile_network_ok_no_self_comunication]
  \\ ho_match_mp_tac trans_pairind
  \\ rw [ compile_network_gen_def
        , procsOf_def
        , procsOf_all_distinct
        , nub'_def
        , reduction_def
        , project_def
        , FILTER_FILTER
        , FOLDL
        , chor_tl_def
        , fupdate_projectS
        , catchup_of_def
        , trans_ln_refl
        , no_self_comunication_def
        , trans_ln_cut_sel_upto
        , dsubst_def]
  (* Com *)
  >- (IMP_RES_TAC lookup_projectS
     \\ rw [trans_ln_def,fupdate_projectS]
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
  >- (rw [trans_ln_def]
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
  >- (rw [trans_ln_def]
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
  >- (rw [trans_ln_def]
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
     \\ qpat_x_assum ‘no_self_comunication _’ kall_tac
     \\ ho_match_mp_tac RTC_SINGLE
     \\ rw [reduction_def]
     \\ ho_match_mp_tac trans_par_l
     \\ ho_match_mp_tac trans_let_gen
     \\ UNABBREV_ALL_TAC
     \\ pop_assum (K ALL_TAC)
     \\ rw []
     >- (Induct_on `vl` \\ rw [lookup_projectS'])
     >- (rw [projectS_fupdate] >> rpt AP_TERM_TAC
        \\ Induct_on `vl` >> rw [lookup_projectS']))
  (* If true *)
  >- (rw []
     \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) (nub' (procsOf c' ⧺ procsOf c2))`
                               , `sq = <|bindings := projectS p s; queue := []|>`
                               ]
     \\ ho_match_mp_tac RTC_TRANS
     \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p c')))
                           (compile_network s (IfThen v p c' c2) l)`
     \\ rw [reduction_def]
     >- (ho_match_mp_tac trans_par_l
        \\ ho_match_mp_tac endpointSemTheory.trans_if_true
        \\ rw [Abbr `sq`,lookup_projectS])
     \\ `¬MEM p l` by rw [Abbr `l`,MEM_FILTER]
     \\ rw [prefix_project_eq]
     \\ match_mp_tac list_trans_com_choice_l'
     \\ Q.ISPECL_THEN [`p`,`sq`,`c'`,`project' p (cut_sel_upto p c')`]
                    mp_tac list_trans_projpre
     \\ impl_tac
     >- (CCONTR_TAC >> fs[] >> imp_res_tac MEM_presel_MEM_procsOf)
     \\ strip_tac
     \\ MAP_EVERY qexists_tac
                  [`(MAP (λ(b,q). LIntChoice p b q) (preSel p c'))`,
                   `(MAP (λ(b,q). LExtChoice p b q) (preSel p c'))`]
     \\ simp[GSYM PULL_EXISTS]
     \\ conj_tac
     >- (simp[EVERY2_MAP,ELIM_UNCURRY]
         \\ match_mp_tac EVERY2_refl \\ Cases \\ rw[])
     \\ simp[compile_network_ok_if_eq]
     \\ qexists_tac
          `FOLDR NPar NNil
            (MAP
               (λproc.
                    NEndpoint proc
                      <|bindings := projectS proc s;
                        queue := preSel_to_queue proc p (preSel p c')|>
                      (project' proc (IfThen v p c' c2))) l)`
     \\ imp_res_tac compile_network_if_l
     \\ simp[compile_network_cut_sel_upto]
     \\ `ALL_DISTINCT l`
          by(qunabbrev_tac `l`
             \\ match_mp_tac FILTER_ALL_DISTINCT
             \\ MATCH_ACCEPT_TAC all_distinct_nub')
     \\ `~MEM p (MAP SND (preSel p c'))`
          by(qhdtm_x_assum `list_trans` mp_tac
             \\ qmatch_goalsub_abbrev_tac `list_trans n1 _ n2`
             \\ rpt(pop_assum kall_tac)
             \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p`,`n1`,`n2`,`c'`]
             \\ Induct \\ rw[preSel_def,list_trans_def]
             \\ imp_res_tac sender_receiver_distinct_choice
             \\ metis_tac[])
     \\ `!x. MEM x (MAP SND(preSel p c')) ==> MEM x l`
          by(qpat_x_assum `¬_` mp_tac \\ qpat_x_assum `¬_` mp_tac
             \\ unabbrev_all_tac \\ rpt(pop_assum kall_tac)
             \\ simp[PULL_FORALL] \\ strip_tac \\ Induct_on `c'`
             \\ rw[preSel_def]
             \\ rw[procsOf_def,nub'_def]
             \\ rw[FILTER_FILTER,FILTER_APPEND_DISTRIB]
             \\ fs[set_nub',MEM_FILTER,MEM_MAP,PULL_EXISTS]
             \\ rveq \\ fs[]
             \\ fs[]
             \\ metis_tac[])
     \\ conj_tac
     >- (`?qf. !proc. (qf:proc ->(proc,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
         \\ `!proc qff. <|bindings := projectS proc s; queue := qff proc|>
                       = <|bindings := projectS proc s; queue := qf proc ++ qff proc|>`
             by(rw[])
         \\ pop_assum mp_tac \\ pop_assum kall_tac
         \\ disch_then (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
         \\ simp[]
         \\ pop_assum mp_tac
         \\ qhdtm_x_assum `ALL_DISTINCT` mp_tac
         \\ rpt(qpat_x_assum `¬_` mp_tac) \\ rpt(pop_assum kall_tac)
         \\ rename1 `MAP SND psl`
         \\ rw [network_consume_LExtChoice])
     \\ `?pn. pn = LENGTH(preSel p c')` by simp[]
     \\ `!proc. MEM proc l ==> project_ok proc (if K T proc then IfThen v p c' c2 else c')`
        by(rw[] >> imp_res_tac compile_network_ok_project_ok)
     \\ ntac 5 (pop_assum mp_tac)
     \\ qpat_x_assum `compile_network_ok _ (IfThen _ _ _ _) _` kall_tac
     \\ qhdtm_x_assum `list_trans` kall_tac
     \\ rpt(qhdtm_x_assum `Abbrev` kall_tac)
     \\ rpt(pop_assum mp_tac)
     \\ `!proc. project' proc (IfThen v p c' c2) = project' proc (if K T proc then IfThen v p c' c2 else c')`
        by(rw[])
     \\ qabbrev_tac `iffy = (K T):proc -> bool`
     \\ pop_assum kall_tac
     \\ pop_assum (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
     \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`s`,`v`,`p`,`c2`,`l`,`c'`,`iffy`,`pn`]
     \\ Induct
     >- (rw[preSel_def,list_trans_def,cut_ext_choice_upto_presel_nil,preSel_to_queue_def]
         >> qmatch_goalsub_abbrev_tac `_ (FOLDR NPar NNil a1) (FOLDR NPar NNil a2)`
         >> `a1 = a2` suffices_by simp[]
         >> unabbrev_all_tac
         >> rw[MAP_EQ_f] >> rw[]
         >> match_mp_tac project_if_l_eq
         >> conj_tac
         >- (first_x_assum drule >> fs[])
         >> conj_tac
         >- (CCONTR_TAC >> fs[])
         >> CCONTR_TAC
         >> fs[] >> rveq >> fs[preSel_def])
     \\ rpt strip_tac
     \\ `?b q c''. c' = Sel p b q c''`
        by(qpat_x_assum `SUC _ = LENGTH _` mp_tac >> Cases_on `c'` >> rw[preSel_def])
     \\ rveq
     \\ `MEM q l` by(fs[preSel_def])
     \\ first_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
     \\ `p <> q` by(CCONTR_TAC >> fs[])
     \\ `project_ok q c''`
        by(imp_res_tac compile_network_ok_project_ok
           \\ rfs[project_def,split_sel_def]
           \\ Cases_on `b` \\ fs[])
     \\ first_assum drule
     \\ strip_tac
     \\ qmatch_goalsub_abbrev_tac `reduction^* (FOLDR NPar NNil (MAP af _))`
     \\ qabbrev_tac `ag = \q. (NEndpoint q <|bindings := projectS q s;
                              queue := preSel_to_queue q p (preSel p c'')|> (project' q c''))`
     \\ `trans (af q) (LTau) (ag q)`
        by(unabbrev_all_tac >> Cases_on `iffy q`
           >> fs[project_def,cut_ext_choice_upto_presel_def,preSel_def,
                 split_sel_def,compile_network_gen_def,preSel_to_queue_def]
           >> rfs[]
           >> rpt(PURE_CASE_TAC \\ fs[] \\ rveq)
           >> simp[cut_ext_choice_upto_presel_def,SPLITP]
           >> TRY(match_mp_tac trans_ext_choice_l_gen
                  >> fs[] >> qexists_tac `[]` >> fs[])
           >> TRY(match_mp_tac trans_ext_choice_r_gen
                  >> fs[] >> qexists_tac `[0w]` >> qexists_tac `[]` >> fs[]))
     \\ `trans (FOLDR NPar NNil ((MAP af l1) ++ af q :: (MAP af l2)))
               LTau (FOLDR NPar NNil ((MAP af l1) ++ ag q :: (MAP af l2)))`
          by(simp[trans_fold_par])
     \\ qabbrev_tac `iffy' = λp. if p = q then F else iffy p`
     \\ qabbrev_tac `ah = (λproc.
                 NEndpoint proc
                   <|bindings := projectS proc s;
                   queue := preSel_to_queue proc p (preSel p c'')|>
                   (project' proc (if iffy' proc then IfThen v p c'' c2 else c'')))`
     \\ match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
     \\ qexists_tac `FOLDR NPar NNil (MAP ah l)`
     \\ conj_tac
     >- (simp[reduction_def]
         \\ `MAP af l1 = MAP ah l1 /\ ag q = ah q /\ MAP af l2 = MAP ah l2`
             suffices_by metis_tac[]
         \\ unabbrev_all_tac
         \\ rw[MAP_EQ_f]
         \\ fs[preSel_def,preSel_to_queue_def,ALL_DISTINCT_APPEND]
         \\ rpt(qpat_x_assum `trans _ _ _` kall_tac)
         \\ `proc <> p` by(CCONTR_TAC >> fs[])
         \\ `proc <> q` by(CCONTR_TAC >> fs[] >> metis_tac[])
         \\ rw[] \\ fs[project_def,split_sel_def])
     \\ first_x_assum (qspecl_then [`iffy'`,`c''`,`l`,`c2`,`p`,`v`,`s`] mp_tac)
     \\ `project_ok p c''` by(fs[project_def])
     \\ `compile_network_ok s c'' l` by(imp_res_tac compile_network_ok_dest_sel)
     \\ rpt(disch_then drule)
     \\ impl_tac
     >- (qpat_x_assum `_ = _ ++ _::_` kall_tac
         >> fs[preSel_def] >> unabbrev_all_tac >> fs[no_self_comunication_def]
         >> rw[] >> rpt(first_x_assum drule) >> simp[]
         >> `proc <> p` by(CCONTR_TAC >> fs[])
         >> fs[project_def,split_sel_def]
         >> rw[])
     \\ qmatch_goalsub_abbrev_tac
          `reduction^* (FOLDR _ _ a1) (FOLDR _ _ a2) ==> reduction^* (FOLDR _ _ a3) (FOLDR _ _ a4)`
     \\ `a1 = a3 /\ a2 = a4` suffices_by metis_tac[]
     \\ unabbrev_all_tac
     \\ rw[MAP_EQ_f,cut_ext_choice_upto_presel_def,preSel_def]
     \\ `proc <> p` by(CCONTR_TAC >> fs[])
     >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
         \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
     >- (fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]
         >> rw[cut_ext_choice_upto_presel_def,SPLITP])
     >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
         \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]))
  (* If false *)
  >- (rw []
     \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) (nub' (procsOf c1 ⧺ procsOf c'))`
                               , `sq = <|bindings := projectS p s; queue := []|>`
                               ]
     \\ ho_match_mp_tac RTC_TRANS
     \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p c')))
                           (compile_network s (IfThen v p c1 c') l)`
     \\ rw [reduction_def]
     >- (ho_match_mp_tac trans_par_l
        \\ ho_match_mp_tac endpointSemTheory.trans_if_false
        \\ rw [Abbr `sq`,lookup_projectS]
        \\ METIS_TAC [lookup_projectS])
     \\ `¬MEM p l` by rw [Abbr `l`,MEM_FILTER]
     \\ rw [prefix_project_eq]
     \\ match_mp_tac list_trans_com_choice_l'
     \\ Q.ISPECL_THEN [`p`,`sq`,`c'`,`project' p (cut_sel_upto p c')`]
                    mp_tac list_trans_projpre
     \\ impl_tac
     >- (CCONTR_TAC >> fs[] >> imp_res_tac MEM_presel_MEM_procsOf)
     \\ strip_tac
     \\ MAP_EVERY qexists_tac
                  [`(MAP (λ(b,q). LIntChoice p b q) (preSel p c'))`,
                   `(MAP (λ(b,q). LExtChoice p b q) (preSel p c'))`]
     \\ simp[GSYM PULL_EXISTS]
     \\ conj_tac
     >- (simp[EVERY2_MAP,ELIM_UNCURRY]
         \\ match_mp_tac EVERY2_refl \\ Cases \\ rw[])
     \\ simp[compile_network_ok_if_eq]
     \\ qexists_tac
          `FOLDR NPar NNil
            (MAP
               (λproc.
                    NEndpoint proc
                      <|bindings := projectS proc s;
                        queue := preSel_to_queue proc p (preSel p c')|>
                      (project' proc (IfThen v p c1 c'))) l)`
     \\ imp_res_tac compile_network_if_r
     \\ simp[compile_network_cut_sel_upto]
     \\ `ALL_DISTINCT l`
          by(qunabbrev_tac `l`
             \\ match_mp_tac FILTER_ALL_DISTINCT
             \\ MATCH_ACCEPT_TAC all_distinct_nub')
     \\ `~MEM p (MAP SND (preSel p c'))`
          by(qhdtm_x_assum `list_trans` mp_tac
             \\ qmatch_goalsub_abbrev_tac `list_trans n1 _ n2`
             \\ rpt(pop_assum kall_tac)
             \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p`,`n1`,`n2`,`c'`]
             \\ Induct \\ rw[preSel_def,list_trans_def]
             \\ imp_res_tac sender_receiver_distinct_choice
             \\ metis_tac[])
     \\ `!x. MEM x (MAP SND(preSel p c')) ==> MEM x l`
          by(qpat_x_assum `¬_` mp_tac \\ qpat_x_assum `¬_` mp_tac
             \\ unabbrev_all_tac \\ rpt(pop_assum kall_tac)
             \\ simp[PULL_FORALL] \\ strip_tac \\ Induct_on `c'`
             \\ rw[preSel_def]
             \\ rw[procsOf_def,nub'_def]
             \\ rw[FILTER_FILTER,FILTER_APPEND_DISTRIB]
             \\ fs[set_nub',MEM_FILTER,MEM_MAP,PULL_EXISTS]
             \\ rveq \\ fs[]
             \\ fs[]
             \\ metis_tac[])
     \\ conj_tac
     >- (`?qf. !proc. (qf:proc ->(proc,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
         \\ `!proc qff. <|bindings := projectS proc s; queue := qff proc|>
                       = <|bindings := projectS proc s; queue := qf proc ++ qff proc|>`
             by(rw[])
         \\ pop_assum mp_tac \\ pop_assum kall_tac
         \\ disch_then (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
         \\ simp[]
         \\ pop_assum mp_tac
         \\ qhdtm_x_assum `ALL_DISTINCT` mp_tac
         \\ rpt(qpat_x_assum `¬_` mp_tac) \\ rpt(pop_assum kall_tac)
         \\ rename1 `MAP SND psl`
         \\ rw [network_consume_LExtChoice])
     \\ `?pn. pn = LENGTH(preSel p c')` by simp[]
     \\ `!proc. MEM proc l ==> project_ok proc (if K T proc then IfThen v p c1 c' else c')`
        by(rw[] >> imp_res_tac compile_network_ok_project_ok)
     \\ ntac 5 (pop_assum mp_tac)
     \\ qpat_x_assum `compile_network_ok _ (IfThen _ _ _ _) _` kall_tac
     \\ qhdtm_x_assum `list_trans` kall_tac
     \\ rpt(qhdtm_x_assum `Abbrev` kall_tac)
     \\ rpt(pop_assum mp_tac)
     \\ `!proc. project' proc (IfThen v p c1 c') = project' proc (if K T proc then IfThen v p c1 c' else c')`
        by(rw[])
     \\ qabbrev_tac `iffy = (K T):proc -> bool`
     \\ pop_assum kall_tac
     \\ pop_assum (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
     \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`w`,`s`,`v`,`p`,`c1`,`l`,`c'`,`iffy`,`pn`]
     \\ Induct
     >- (rw[preSel_def,list_trans_def,cut_ext_choice_upto_presel_nil,preSel_to_queue_def]
         >> qmatch_goalsub_abbrev_tac `_ (FOLDR NPar NNil a1) (FOLDR NPar NNil a2)`
         >> `a1 = a2` suffices_by simp[]
         >> unabbrev_all_tac
         >> rw[MAP_EQ_f] >> rw[]
         >> match_mp_tac project_if_r_eq
         >> conj_tac
         >- (first_x_assum drule >> fs[])
         >> conj_tac
         >- (CCONTR_TAC >> fs[])
         >> CCONTR_TAC
         >> fs[] >> rveq >> fs[preSel_def])
     \\ rpt strip_tac
     \\ `?b q c''. c' = Sel p b q c''`
        by(qpat_x_assum `SUC _ = LENGTH _` mp_tac >> Cases_on `c'` >> rw[preSel_def])
     \\ rveq
     \\ `MEM q l` by(fs[preSel_def])
     \\ first_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
     \\ `p <> q` by(CCONTR_TAC >> fs[])
     \\ `project_ok q c''`
        by(imp_res_tac compile_network_ok_project_ok
           \\ rfs[project_def,split_sel_def]
           \\ Cases_on `b` \\ fs[])
     \\ first_assum drule
     \\ strip_tac
     \\ qmatch_goalsub_abbrev_tac `reduction^* (FOLDR NPar NNil (MAP af _))`
     \\ qabbrev_tac `ag = \q. (NEndpoint q <|bindings := projectS q s;
                              queue := preSel_to_queue q p (preSel p c'')|> (project' q c''))`
     \\ `trans (af q) (LTau) (ag q)`
        by(unabbrev_all_tac >> Cases_on `iffy q`
           >> fs[project_def,cut_ext_choice_upto_presel_def,preSel_def,
                 split_sel_def,compile_network_gen_def,preSel_to_queue_def]
           >> rfs[]
           >> rpt(PURE_CASE_TAC \\ fs[] \\ rveq)
           >> simp[cut_ext_choice_upto_presel_def,SPLITP]
           >> TRY(match_mp_tac trans_ext_choice_l_gen
                  >> fs[] >> qexists_tac `[]` >> fs[])
           >> TRY(match_mp_tac trans_ext_choice_r_gen
                  >> fs[] >> qexists_tac `[0w]` >> qexists_tac `[]` >> fs[]))
     \\ `trans (FOLDR NPar NNil ((MAP af l1) ++ af q :: (MAP af l2)))
               LTau (FOLDR NPar NNil ((MAP af l1) ++ ag q :: (MAP af l2)))`
          by(simp[trans_fold_par])
     \\ qabbrev_tac `iffy' = λp. if p = q then F else iffy p`
     \\ qabbrev_tac `ah = (λproc.
                 NEndpoint proc
                   <|bindings := projectS proc s;
                   queue := preSel_to_queue proc p (preSel p c'')|>
                   (project' proc (if iffy' proc then IfThen v p c1 c'' else c'')))`
     \\ match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
     \\ qexists_tac `FOLDR NPar NNil (MAP ah l)`
     \\ conj_tac
     >- (simp[reduction_def]
         \\ `MAP af l1 = MAP ah l1 /\ ag q = ah q /\ MAP af l2 = MAP ah l2`
             suffices_by metis_tac[]
         \\ unabbrev_all_tac
         \\ rw[MAP_EQ_f]
         \\ fs[preSel_def,preSel_to_queue_def,ALL_DISTINCT_APPEND]
         \\ rpt(qpat_x_assum `trans _ _ _` kall_tac)
         \\ `proc <> p` by(CCONTR_TAC >> fs[])
         \\ `proc <> q` by(CCONTR_TAC >> fs[] >> metis_tac[])
         \\ rw[] \\ fs[project_def,split_sel_def])
     \\ first_x_assum (qspecl_then [`iffy'`,`c''`,`l`,`c1`,`p`,`v`,`s`,`w`] mp_tac)
     \\ `project_ok p c''` by(fs[project_def])
     \\ `compile_network_ok s c'' l` by(imp_res_tac compile_network_ok_dest_sel)
     \\ rpt(disch_then drule)
     \\ impl_tac
     >- (qpat_x_assum `_ = _ ++ _::_` kall_tac
         >> fs[preSel_def] >> unabbrev_all_tac >> fs[no_self_comunication_def]
         >> rw[] >> rpt(first_x_assum drule) >> simp[]
         >> `proc <> p` by(CCONTR_TAC >> fs[])
         >> fs[project_def,split_sel_def]
         >> rw[])
     \\ qmatch_goalsub_abbrev_tac
          `reduction^* (FOLDR _ _ a1) (FOLDR _ _ a2) ==> reduction^* (FOLDR _ _ a3) (FOLDR _ _ a4)`
     \\ `a1 = a3 /\ a2 = a4` suffices_by metis_tac[]
     \\ unabbrev_all_tac
     \\ rw[MAP_EQ_f,cut_ext_choice_upto_presel_def,preSel_def]
     \\ `proc <> p` by(CCONTR_TAC >> fs[])
     >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
         \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
     >- (fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]
         >> rw[cut_ext_choice_upto_presel_def,SPLITP])
     >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
         \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]))
  \\ TRY (simp [trans_ln_catchup_of_pair,no_self_comunication_def] \\ NO_TAC)
  >- (CCONTR_TAC
      \\ qpat_x_assum ‘p ∉ _’ mp_tac
      \\ qpat_x_assum ‘trans _ (α,[]) _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ map_every qid_spec_tac [‘s’,‘v’,‘p’,‘c'''’,‘α’]
      \\ Induct_on ‘c''’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      >- metis_tac []
      >- (first_x_assum drule \\ simp [freeprocs_def])
      \\ qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chor_size”)
      \\ EVAL_TAC \\ fs [])
  >- (fs [lcong_nil_simp]
      \\ CCONTR_TAC
      \\ qpat_x_assum ‘p ∉ _’ mp_tac
      \\ qpat_x_assum ‘trans _ (α,[]) _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ map_every qid_spec_tac [‘s’,‘v’,‘p’,‘c''’,‘α’]
      \\ Induct_on ‘c'''’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      >- metis_tac [lcong_nil_simp]
      >- (qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chor_size”)
          \\ EVAL_TAC \\ fs [])
      \\ first_x_assum drule \\ simp [freeprocs_def])
  >- (Cases_on ‘α ≠ LFix’
      >- (drule trans_not_eq \\ fs [])
      \\ gs [catchup_of_def,project_def])
  >- (CCONTR_TAC
      \\ ntac 5 (pop_assum kall_tac)
      \\ last_x_assum kall_tac
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p1’,‘v1’,‘p2’,‘v2’,‘α’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  >- (CCONTR_TAC
      \\ ntac 5 (pop_assum kall_tac)
      \\ last_x_assum kall_tac
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p1’,‘v1’,‘p2’,‘v2’,‘α’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  >- (CCONTR_TAC
      \\ ntac 5 (pop_assum kall_tac)
      \\ last_x_assum kall_tac
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p1’,‘v1’,‘p2’,‘v2’,‘α’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  >- (CCONTR_TAC
      \\ ntac 4 (pop_assum kall_tac)
      \\ rpt (pop_assum mp_tac)
      \\ map_every qid_spec_tac [‘s’,‘p’,‘v’,‘f’,‘vl’]
      \\ Induct_on ‘c'’ \\ simp []
      \\ ONCE_REWRITE_TAC [trans_cases]
      \\ rw [freeprocs_def]
      \\ rw [freeprocs_def]
      \\ fs[freeprocs_def]
      \\ fs[project_def]
      \\ rw[]
      \\ res_tac
      \\ rfs[])
  (* TODO: Fix *)
  >- (qmatch_goalsub_abbrev_tac ‘compile_network s _ l’
      \\ pop_assum kall_tac
      \\ Induct_on ‘l’
      \\ rw [compile_network_gen_def]
      \\ gs []
      \\ qmatch_goalsub_abbrev_tac ‘reduction^* (NPar a1 b1) (NPar a2 b2)’
      \\ irule RTC_SPLIT
      \\ qexists_tac ‘NPar a1 b2’
      \\ conj_tac
      >- (irule reduction_par_r \\ simp [])
      \\ irule reduction_par_l
      \\ unabbrev_all_tac
      \\simp [project_def] \\ rw []
      >- (irule RTC_TRANS \\ simp [reduction_def]
          \\ irule_at Any endpointSemTheory.trans_fix
          \\ cheat (* TODO: project distributes over dsubst *))
      \\ qspecl_then [‘c’,‘h’,‘dn’,‘dn’] assume_tac procsOf_dsubst_MEM_eq
      \\ cheat)
  (* TODO: Prove that LFix can not remove stuff at the front of the choreography *)
  >- (qpat_x_assum ‘trans _ _ _’ (assume_tac o ONCE_REWRITE_RULE [trans_cases])
      \\ fs [] \\ cheat)
  >- (qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chor_size”)
      \\ EVAL_TAC \\ fs [])
  >- (qpat_x_assum ‘_ = _’ (mp_tac o AP_TERM “chor_size”)
      \\ EVAL_TAC \\ fs [])
  (* TODO:  Prove that LFix can not remove stuff at the front of the choreography *)
  \\ cheat
QED

Theorem split_sel_nonproc_NONE:
  ∀p p1 c.
  ~MEM p (procsOf c) ⇒ split_sel p p1 c = NONE
Proof
  ho_match_mp_tac split_sel_ind >>
  rw[procsOf_def,MEM_nub'] >>
  fs[split_sel_def]
QED

Theorem procsOf_catchup_of:
  MEM h (procsOf (catchup_of α c)) ⇒ MEM h (procsOf c)
Proof
  Cases_on ‘α’ >> fs[catchup_of_def] >>
  Induct_on ‘c’ >> fs[procsOf_def,cut_sel_upto_def] >>
  rw[MEM_nub'] >>
  fs[procsOf_def,MEM_nub']
QED

Theorem trans_procsOf:
  ∀s c α l s' c' p.
  trans (s,c) (α,l) (s',c') ∧ MEM p (procsOf c') ⇒ MEM p (procsOf c)
Proof
  simp[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_pairind >>
  rw[procsOf_def,MEM_nub'] >>
  simp[]
QED

Theorem trans_label_procsOf_written:
  ∀s c α l s' c' x.
  trans (s,c) (α,l) (s',c') ∧ ~MEM h (procsOf c) ⇒
  written α ≠ SOME (x,h)
Proof
  simp[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_pairind >>
  rw[procsOf_def,MEM_nub'] >>
  simp[written_def]
QED

Theorem compile_network_preservation_ln_gen:
   ∀s c α s' c' ps. compile_network_ok s c ps
    ∧ trans (s,c) (α,[]) (s',c') ∧ chor_tl s c = (s',c')
    ∧ set (procsOf c) ⊆ set ps ∧ ALL_DISTINCT ps
    ⇒ trans_ln (s',c') (s',catchup_of α c')
       ∧ reduction^* (compile_network s  c ps)
                      (compile_network s' (catchup_of α c') ps)
Proof
  rpt GEN_TAC >> disch_then strip_assume_tac >>
  imp_res_tac compile_network_ok_subset >>
  drule_all_then strip_assume_tac compile_network_preservation_ln >>
  simp[] >>
  qspecl_then [‘λp. MEM p (procsOf c)’,‘ps’] assume_tac PERM_SPLIT >>
  ‘PERM (FILTER (λp. MEM p (procsOf c)) ps) (procsOf c)’
    by(match_mp_tac PERM_ALL_DISTINCT >>
       rw[ALL_DISTINCT_FILTER,MEM_FILTER,FILTER_FILTER,EQ_IMP_THM] >>
       fs[SUBSET_DEF] >> res_tac >> fs[] >-
         (pop_assum(strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
          fs[ALL_DISTINCT_APPEND,FILTER_APPEND,APPEND_EQ_SING] >>
          fs[FILTER_EQ_NIL,EVERY_MEM]) >>
       ‘ALL_DISTINCT (procsOf c)’ by(simp[procsOf_all_distinct]) >>
       qpat_x_assum ‘MEM _ (procsOf _)’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
       fs[ALL_DISTINCT_APPEND,FILTER_APPEND,APPEND_EQ_SING] >>
       fs[FILTER_EQ_NIL,EVERY_MEM]) >>
  drule PERM_CONG >>
  disch_then(qspecl_then [‘FILTER ($~ ∘ (λp. MEM p (procsOf c))) ps’,‘FILTER ($~ ∘ (λp. MEM p (procsOf c))) ps’] mp_tac) >>
  simp[PERM_REFL] >>
  strip_tac >>
  dxrule_all PERM_TRANS >>
  pop_assum kall_tac >>
  strip_tac >>
  fs[Once PERM_SYM] >>
  match_mp_tac PERM_chor_compile_network_reduction' >>
  goal_assum drule >>
  conj_tac >-
    (drule ALL_DISTINCT_PERM >> simp[]) >>
  rename1 ‘procsOf c ++ rest’ >>
  match_mp_tac PERM_chor_compile_network_reduction' >>
  qexists_tac ‘rest ++ procsOf c’ >> simp[PERM_APPEND] >>
  conj_asm1_tac >- (drule ALL_DISTINCT_PERM >> disch_then(mp_tac o GSYM) >>
                    rw[] >> fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qhdtm_x_assum ‘PERM’ kall_tac >>
  Induct_on ‘rest’ >>
  simp[] >>
  rw[] >>
  res_tac >>
  simp[compile_network_gen_def] >>
  drule_then (mp_tac o ONCE_REWRITE_RULE[MONO_NOT_EQ]) trans_procsOf >>
  disch_then drule >>
  strip_tac >>
  drule (CONTRAPOS procsOf_catchup_of) >>
  disch_then(qspec_then ‘α’ assume_tac) >>
  simp[project_nonmember_nil] >>
  ‘projectS h s = projectS h s'’
    by(rw[fmap_eq_flookup,GSYM lookup_projectS'] >>
       CONV_TAC SYM_CONV >>
       drule_then match_mp_tac lookup_unwritten_after_trans_tup >>
       drule_then match_mp_tac trans_label_procsOf_written >>
       simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  match_mp_tac reduction_par_r >>
  simp[]
QED

Theorem compile_network_ok_chor_tl:
  ∀s c ps s' c'.
  compile_network_ok s c ps ∧ chor_tl s c = (s',c') ⇒
  compile_network_ok s' c' ps
Proof
  Induct_on ‘ps’ >> rw[compile_network_gen_def] >>
  res_tac >>
  Cases_on ‘c’ >> fs[chor_tl_def,project_def,AllCaseEqs()] >> rveq >>
  fs[project_def] >>
  rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
  metis_tac[split_sel_project_ok,split_sel_project_ok2]
QED

Definition trans_ln_cut_def:
  trans_ln_cut = (λp r. ∃τ q. trans p (τ,[]) q ∧
                 q = UNCURRY chor_tl p ∧
                 r = (FST q, catchup_of τ (SND q)))⃰
End

Theorem compile_network_ok_catchup_of:
  compile_network_ok s c ps ⇒
  compile_network_ok s (catchup_of τ c) ps
Proof
  Cases_on ‘τ’ >> fs[catchup_of_def] >>
  Induct_on ‘c’ >> fs[cut_sel_upto_def] >>
  rw[] >>
  drule compile_network_ok_dest_sel >>
  simp[]
QED

Theorem compile_network_preservation_trans_ln_cut:
  ∀s c s' c'.
    compile_network_ok s  c (procsOf c) ∧
    trans_ln_cut (s,c) (s',c')
    ⇒ ∃s'' c''. trans_ln_cut (s',c') (s'',c'')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'' c'' (procsOf c))
Proof
   ‘∀p q.
    trans_ln_cut p q
    ⇒ ∀s c s' c' ps.
       compile_network_ok s  c ps ∧
       p = (s,c) ∧ q = (s',c') ∧ set(procsOf c) ⊆ set(ps) ∧ ALL_DISTINCT ps
       ⇒ ∃s'' c''.
          trans_ln_cut (s',c') (s'',c'') ∧
          reduction^* (compile_network s   c   ps)
                      (compile_network s'' c'' ps)’
   suffices_by metis_tac [SUBSET_REFL,procsOf_all_distinct]
   \\ ntac 3 strip_tac
   \\ pop_assum (mp_tac o REWRITE_RULE [trans_ln_cut_def])
   \\ map_every qid_spec_tac [‘q’,‘p’]
   \\ ho_match_mp_tac RTC_strongind
   \\ rw []
   >- (map_every qexists_tac [‘s’,‘c’] \\ fs [trans_ln_cut_def])
   \\ fs [GSYM trans_ln_cut_def]
   \\ Cases_on ‘chor_tl s c’
   \\ drule_all compile_network_preservation_ln_gen
   \\ rw [] \\ fs []
   \\ ‘compile_network_ok q (catchup_of τ r) ps’
        by metis_tac[compile_network_ok_chor_tl,compile_network_ok_catchup_of]
   \\ first_x_assum drule
   \\ impl_tac
   >- (simp[] >>
       fs[SUBSET_DEF] >> rw[] >> imp_res_tac procsOf_catchup_of >>
       imp_res_tac trans_procsOf >> res_tac)
   \\ strip_tac
   \\ metis_tac[RTC_RTC]
QED

Theorem no_self_comunication_cut_sel_upto:
  !p c. no_self_comunication c ==> no_self_comunication(cut_sel_upto p c)
Proof
  Induct_on `c` >> rw[cut_sel_upto_def,no_self_comunication_def]
QED

Theorem no_undefined_vars_cut_sel_upto:
  !p c. no_undefined_vars (s,c) ==> no_undefined_vars(s,cut_sel_upto p c)
Proof
  Induct_on `c` >> rw[cut_sel_upto_def,no_undefined_vars_def,free_variables_def] >>
  metis_tac[no_undefined_vars_def]
QED

Theorem no_self_comunication_catchup_of:
  ∀p τ.
  no_self_comunication p ⇒
  no_self_comunication (catchup_of τ p)
Proof
  Cases_on ‘τ’ >> fs[catchup_of_def] >>
  metis_tac[no_self_comunication_cut_sel_upto]
QED

Theorem no_self_comunication_chor_tl:
  ∀p.
  no_self_comunication(SND p) ⇒
  no_self_comunication (SND(UNCURRY chor_tl p))
Proof
  PairCases >> Cases_on ‘p1’ >> rw[no_self_comunication_def,chor_tl_def]
QED

Theorem trans_ln_cut_IMP_trans_ln:
  ∀p q.
  trans_ln_cut p q ∧ no_self_comunication(SND p) ⇒ trans_ln p q
Proof
  simp[trans_ln_cut_def,trans_ln_def,GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[] >>
  fs[] >>
  imp_res_tac no_self_comunication_chor_tl >>
  drule_then(qspec_then ‘τ’ mp_tac) no_self_comunication_catchup_of >>
  strip_tac >>
  fs[] >>
  match_mp_tac RTC_TRANS >>
  simp[PULL_EXISTS] >>
  goal_assum drule >>
  pop_assum kall_tac >>
  drule trans_ln_catchup_of >>
  disch_then(qspec_then ‘τ’ strip_assume_tac) >>
  match_mp_tac(MP_CANON RTC_RTC) >>
  fs[trans_ln_def] >>
  goal_assum drule >>
  simp[]
QED

Theorem NRC_catchup:
  ∀p c s.
  no_self_comunication c ⇒
  NRC (λp q. ∃τ. trans p (τ,[]) q ∧ q = UNCURRY chor_tl p)
      (LENGTH (preSel p c))
      (s,c) (s,cut_sel_upto p c)
Proof
  ho_match_mp_tac(fetch "-" "preSel_ind") >> rw[] >>
  rw[preSel_def,NRC,chor_tl_def,PULL_EXISTS] >>
  fs[no_self_comunication_def] >>
  res_tac >>
  simp[Once cut_sel_upto_def] >>
  metis_tac[trans_rules]
QED

Theorem NRC_trans_ln_eq_deriv:
  ∀n p q r.
  NRC (λp q. ∃τ. trans p (τ,[]) q ∧ q = UNCURRY chor_tl p) n p q ∧
  NRC (λp q. ∃τ. trans p (τ,[]) q ∧ q = UNCURRY chor_tl p) n p r ⇒
  q = r
Proof
  Induct >> rw[] >>
  fs[NRC] >> res_tac >>
  rveq >>
  res_tac
QED

Theorem trans_ln_IMP_trans_ln_cut:
  ∀p q.
  trans_ln p q ∧ no_self_comunication(SND p) ⇒ ∃q'. trans_ln_cut p q' ∧ trans_ln q q'
Proof
  simp[Once trans_ln_def,GSYM AND_IMP_INTRO,GSYM PULL_FORALL,RTC_eq_NRC,PULL_EXISTS] >>
  CONV_TAC(RESORT_FORALL_CONV List.rev) >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  Cases >> rw[NRC] >-
    (metis_tac[trans_ln_cut_def,trans_ln_def,RTC_REFL]) >>
  imp_res_tac no_self_comunication_chor_tl >>
  rename1 ‘SUC n’ >>
  Cases_on ‘τ’ >-
    (rename1 ‘LTau proc v’ >>
     Cases_on ‘LENGTH(preSel proc (SND(UNCURRY chor_tl p))) > n’ >-
       (drule NRC_catchup >>
        disch_then(qspecl_then [‘proc’,‘FST(UNCURRY chor_tl p)’] mp_tac) >>
        strip_tac >>
        fs[PAIR] >>
        qmatch_asmsub_abbrev_tac ‘NRC _ _ _ a1’ >> qexists_tac ‘a1’ >>
        qunabbrev_tac ‘a1’ >>
        conj_tac >-
         (simp[trans_ln_cut_def] >>
          match_mp_tac RTC_SUBSET >>
          simp[] >>
          goal_assum drule >>
          simp[catchup_of_def]) >>
        fs[GREATER_DEF] >>
        imp_res_tac LESS_ADD >>
        pop_assum(SUBST_ALL_TAC o GSYM) >>
        FULL_SIMP_TAC std_ss [Once ADD_SYM] >>
        FULL_SIMP_TAC std_ss [NRC_ADD_EQN] >>
        pop_assum mp_tac >>
        drule NRC_trans_ln_eq_deriv >>
        disch_then(last_assum o mp_then Any mp_tac) >>
        rpt strip_tac >> rveq >>
        simp[trans_ln_def] >>
        match_mp_tac NRC_RTC >>
        goal_assum drule) >>
     fs[GREATER_DEF,NOT_LESS] >>
     imp_res_tac LESS_EQ_ADD_EXISTS >>
     rveq >>
     FULL_SIMP_TAC std_ss [Once ADD_SYM] >>
     FULL_SIMP_TAC std_ss [NRC_ADD_EQN] >>
     drule NRC_catchup >>
     disch_then(qspecl_then [‘proc’,‘FST(UNCURRY chor_tl p)’] mp_tac) >>
     strip_tac >>
     fs[PAIR] >>
     drule NRC_trans_ln_eq_deriv >>
     disch_then(last_assum o mp_then Any mp_tac) >>
     strip_tac >> rveq >> fs[] >>
     first_x_assum(qspec_then ‘p'’ mp_tac) >>
     impl_tac >- simp[] >>
     disch_then drule >>
     impl_tac >- (simp[] >> metis_tac[no_self_comunication_cut_sel_upto]) >>
     strip_tac >>
     simp[Once CONJ_SYM] >> goal_assum drule >>
     fs[trans_ln_cut_def] >>
     match_mp_tac RTC_TRANS >>
     simp[PULL_EXISTS] >> goal_assum drule >>
     simp[PULL_EXISTS,catchup_of_def]) >>
  first_x_assum(qspec_then ‘n’ mp_tac) >>
  simp[] >> disch_then drule >>
  simp[] >>
  strip_tac >>
  qexists_tac ‘q'’ >> simp[] >>
  simp[trans_ln_cut_def] >>
  match_mp_tac RTC_TRANS >>
  fs[trans_ln_cut_def] >>
  simp[Once CONJ_SYM] >>
  goal_assum drule >>
  goal_assum drule >>
  simp[catchup_of_def]
QED

Theorem trans_ln_no_self_comunication:
  ∀sc sc'.
  trans_ln sc sc' ∧ no_self_comunication (SND sc) ⇒
  no_self_comunication(SND sc')
Proof
  simp[trans_ln_def,Once CONJ_SYM] >>
  ho_match_mp_tac RTC_lifts_invariants >>
  rpt PairCases >>
  rw[] >>
  imp_res_tac no_self_comunication_trans_pres
QED

Theorem compile_network_preservation_trans_ln:
  ∀s c s' c' pn.
    compile_network_ok s  c (procsOf c) ∧
    trans_ln (s,c) (s',c')
    ⇒ ∃s'' c''. trans_ln (s',c') (s'',c'')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'' c'' (procsOf c))
Proof
  rpt strip_tac >>
  drule trans_ln_IMP_trans_ln_cut >>
  impl_tac >- metis_tac[compile_network_ok_no_self_comunication,SND] >>
  strip_tac >>
  drule compile_network_preservation_trans_ln_cut >>
  rename1 ‘trans_ln_cut (s,c) sc’ >>
  PairCases_on ‘sc’ >>
  disch_then drule >>
  strip_tac >>
  drule trans_ln_cut_IMP_trans_ln >>
  impl_tac >-
    (drule compile_network_ok_no_self_comunication >>
     strip_tac >>
     imp_res_tac trans_ln_no_self_comunication >>
     fs[]) >>
  strip_tac >>
  drule_then drule trans_ln_trans_ln >>
  strip_tac >>
  goal_assum drule >>
  simp[]
QED

Theorem compile_network_ok_project_ok:
  !s c pn. compile_network_ok s c pn <=> (!p. MEM p pn ==> project_ok p c)
Proof
  simp[EQ_IMP_THM,FORALL_AND_THM] >> conj_tac >>
  Induct_on `pn` >>
  rw[compile_network_gen_def] >> simp[] >>
  res_tac
QED

Theorem chor_size_cut_sel_upto:
  !p c. chor_to_endpoint$chor_size (cut_sel_upto p c) <= chor_to_endpoint$chor_size c
Proof
  strip_tac >> Induct_on `c` >> rw[cut_sel_upto_def,chor_size_def] >> intLib.COOPER_TAC
QED

Theorem project_ok_cut_sel_upto:
  !p' c1 p.
  project_ok p' c1 ==>
  project_ok p' (cut_sel_upto p c1)
Proof
  Induct_on `c1` >> rw[cut_sel_upto_def] >>
  fs[project_def] >>
  every_case_tac >> fs[]
QED

Theorem procsOf_cut_sel_upto:
  !p c1.
  set(procsOf(cut_sel_upto p c1)) ⊆ set(procsOf c1)
Proof
  Induct_on `c1` >> rw[cut_sel_upto_def,procsOf_def,set_nub'] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem compile_network_project:
  !s v p c' c2 l.
   compile_network s c l =
   FOLDR NPar NNil
   (MAP (λproc. NEndpoint proc (<| bindings := projectS proc s;
                                   queue    := [] |>) (project' proc c)) l)
Proof
   Induct_on `l`
   >- rw[compile_network_gen_def]
   >> rpt strip_tac
   >> fs[compile_network_gen_def]
   >> fs[project_def]
QED

Theorem compile_network_reflection_lemma:
  ∀s c pn.
    compile_network_ok s c pn
    ∧ ALL_DISTINCT pn
    ∧ set(procsOf c) ⊆ set pn
    ∧ no_undefined_vars (s,c)
    ∧ no_self_comunication c
    ==> ∃s'' p2.
             reduction^* (compile_network s c pn) p2
             ∧ trans_s (s,c) (s'',Nil)
             ∧ p2 = compile_network s'' Nil pn
Proof
  `∀cs s c pn.
    cs = chor_to_endpoint$chor_size c
    ∧ compile_network_ok s c pn
    ∧ ALL_DISTINCT pn
    ∧ set(procsOf c) ⊆ set pn
    ∧ no_undefined_vars (s,c)
    ∧ no_self_comunication c
    ==> ∃s'' p2.
             reduction^* (compile_network s c pn) p2
             ∧ trans_s (s,c) (s'',Nil)
             ∧ p2 = compile_network s'' Nil pn`
    suffices_by metis_tac[compile_network_ok_no_self_comunication] >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rpt strip_tac >>
  Cases_on `c` >-
    ((* Nil *)
      MAP_EVERY qexists_tac [`s`,`compile_network s Nil pn`] >> simp[trans_s_def]) >-
    ((* IfThen *)
     rename1 `IfThen v p c1 c2` >>
     `?d. FLOOKUP s (v,p) = SOME d`
       by(fs[no_undefined_vars_def,free_variables_def] >>
          imp_res_tac FDOM_FLOOKUP >> goal_assum drule) >>
     Cases_on `d = [1w]` >-
       (first_x_assum(qspec_then `chor_to_endpoint$chor_size(cut_sel_upto p c1)` mp_tac) >>
        impl_tac >-
          (fs[chor_size_def] >>
           match_mp_tac LESS_EQ_LESS_TRANS >>
           qspecl_then [`p`,`c1`] assume_tac chor_size_cut_sel_upto >>
           goal_assum drule >> simp[]) >>
        disch_then(qspecl_then [`s`,`cut_sel_upto p c1`,`pn`] mp_tac) >>
        impl_tac >-
          (simp[] >>
           conj_tac >-
             (dxrule_then assume_tac compile_network_if_l >>
              fs[compile_network_ok_project_ok] >>
              rw[] >>
              res_tac >>
              match_mp_tac project_ok_cut_sel_upto >> simp[]) >>
           conj_tac >- (fs[procsOf_def,set_nub'] >> metis_tac[SUBSET_TRANS,procsOf_cut_sel_upto]) >>
           conj_tac >- (match_mp_tac no_undefined_vars_cut_sel_upto >>
                        fs[no_undefined_vars_def,free_variables_def]) >>
           match_mp_tac no_self_comunication_cut_sel_upto >>
           fs[no_self_comunication_def]) >>
        strip_tac >>
        rveq >>
        qexists_tac `s''` >>
        qexists_tac `compile_network s'' Nil pn` >>
        conj_tac >-
          (match_mp_tac(MP_CANON RTC_RTC) >> HINT_EXISTS_TAC >> simp[] >>
           qpat_x_assum `reduction^* _ _` kall_tac >>
           match_mp_tac PERM_chor_compile_network_reduction >>
           qexists_tac `p::FILTER (λy. p ≠ y) pn` >>
           conj_tac >-
             (fs[SUBSET_DEF,procsOf_def,set_nub',DISJ_IMP_THM,FORALL_AND_THM] >>
              qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
              rveq >> fs[ALL_DISTINCT_APPEND,FILTER_APPEND] >>
              fs[PERM_CONS_EQ_APPEND] >>
              qexists_tac `l1` >> qexists_tac `l2` >>
              fs[] >>
              match_mp_tac PERM_INTRO >>
              rw[APPEND_EQ_APPEND,PULL_EXISTS] >>
              disj1_tac >> qexists_tac `[]` >>
              simp[FILTER_EQ_ID] >>
              rw[EVERY_MEM] >>
              metis_tac[]) >>
           conj_tac >- (rw[MEM_FILTER,FILTER_ALL_DISTINCT]) >>
           rw[compile_network_gen_def,project_def]
           \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) pn`
                                     , `sq = <|bindings := projectS p s; queue := []|>`]
           \\ ho_match_mp_tac RTC_TRANS
           \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p c1)))
                           (compile_network s (IfThen v p c1 c2) l)`
           \\ rw [reduction_def]
           >- (ho_match_mp_tac trans_par_l
               \\ ho_match_mp_tac endpointSemTheory.trans_if_true
               \\ rw [Abbr `sq`,lookup_projectS])
           \\ `¬MEM p l` by rw [Abbr `l`,MEM_FILTER]
           \\ `MEM p pn` by(fs[procsOf_def,SUBSET_DEF,set_nub'])
           \\ drule_then (strip_assume_tac o REWRITE_RULE [compile_network_ok_project_ok]) compile_network_if_l
           \\ first_x_assum (drule_then assume_tac)
           \\ rw [prefix_project_eq]
           \\ match_mp_tac list_trans_com_choice_l'
           \\ Q.ISPECL_THEN [`p`,`sq`,`c1`,`project' p (cut_sel_upto p c1)`]
                          mp_tac list_trans_projpre
           \\ impl_tac
           >- (CCONTR_TAC >> fs[] >> imp_res_tac MEM_presel_MEM_procsOf >>
               drule compile_network_if_l >>
               metis_tac[compile_network_ok_project_ok])
           \\ strip_tac
           \\ MAP_EVERY qexists_tac
                        [`(MAP (λ(b,q). LIntChoice p b q) (preSel p c1))`,
                         `(MAP (λ(b,q). LExtChoice p b q) (preSel p c1))`]
           \\ simp[GSYM PULL_EXISTS]
           \\ conj_tac
           >- (simp[EVERY2_MAP,ELIM_UNCURRY]
               \\ match_mp_tac EVERY2_refl \\ Cases \\ rw[])
           \\ simp[compile_network_ok_if_eq]
           \\ qexists_tac
              `FOLDR NPar NNil
                (MAP
                   (λproc.
                        NEndpoint proc
                          <|bindings := projectS proc s;
                            queue := preSel_to_queue proc p (preSel p c1)|>
                          (project' proc (IfThen v p c1 c2))) l)`
           \\ imp_res_tac compile_network_if_l
           \\ simp[compile_network_cut_sel_upto]
           \\ `ALL_DISTINCT l`
              by(qunabbrev_tac `l`
                 \\ match_mp_tac FILTER_ALL_DISTINCT \\ simp[])
           \\ `~MEM p (MAP SND (preSel p c1))`
                by(qhdtm_x_assum `list_trans` mp_tac
                   \\ qmatch_goalsub_abbrev_tac `list_trans n1 _ n2`
                   \\ rpt(pop_assum kall_tac)
                   \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p`,`n1`,`n2`,`c1`]
                   \\ Induct \\ rw[preSel_def,list_trans_def]
                   \\ imp_res_tac sender_receiver_distinct_choice
                   \\ metis_tac[])
           \\ `!x. MEM x (MAP SND(preSel p c1)) ==> MEM x l`
                by(qpat_x_assum `¬_` mp_tac \\ qpat_x_assum `¬_` mp_tac
                   \\ unabbrev_all_tac\\ fs[procsOf_def,set_nub']
                   \\ qpat_x_assum `set (procsOf c1) ⊆ set pn` mp_tac
                   \\ rpt(pop_assum kall_tac)
                   \\ simp[PULL_FORALL] \\ strip_tac \\ Induct_on `c1`
                   \\ rw[preSel_def]
                   \\ fs[procsOf_def,set_nub']
                   \\ rw[MEM_FILTER])
           \\ conj_tac
           >- (rw[compile_network_project]
               \\ `?qf. !proc. (qf:proc ->(proc,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
               \\ `!proc qff. <|bindings := projectS proc s; queue := qff proc|>
                             = <|bindings := projectS proc s; queue := qf proc ++ qff proc|>`
                   by(rw[])
               \\ pop_assum mp_tac \\ pop_assum kall_tac
               \\ disch_then (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
               \\ simp[]
               \\ pop_assum mp_tac
               \\ qhdtm_x_assum `ALL_DISTINCT` mp_tac
               \\ rpt(qpat_x_assum `¬_` mp_tac)
               \\ rename1 `MAP SND psl`
               \\ pop_assum mp_tac
               \\ rpt(pop_assum kall_tac)
               \\ rw[network_consume_LExtChoice])
           \\ `compile_network_ok s (IfThen v p c1 c2) l`
              by(fs[compile_network_ok_project_ok] >> rw[] >>
                 first_x_assum match_mp_tac >> fs[Abbr `l`,MEM_FILTER])
           \\ `!proc. MEM proc l ==> project_ok proc (if K T proc then IfThen v p c1 c2 else c1)`
              by(rw[] >> fs[compile_network_ok_project_ok] >> res_tac)
           \\ rename1 `_ ⊆ set ppn`
           \\ `?pn. pn = LENGTH(preSel p c1)` by simp[]
           \\ drule_then assume_tac compile_network_if_l
           \\ simp[compile_network_cut_sel_upto]
           \\ pop_assum kall_tac
           \\ ntac 2 (pop_assum mp_tac)
           \\ dxrule compile_network_if_l
           \\ ntac 3 (pop_assum mp_tac)
           \\ qhdtm_x_assum `list_trans` kall_tac
           \\ rpt(qhdtm_x_assum `Abbrev` kall_tac)
           \\ qpat_x_assum `~MEM p l` mp_tac
           \\ qpat_x_assum `project_ok _ _` mp_tac
           \\ drule_then (assume_tac o REWRITE_RULE[compile_network_ok_project_ok]) compile_network_if_r
           \\ pop_assum drule
           \\ rpt(pop_assum kall_tac) (* ? *)
           \\ `!proc. project' proc (IfThen v p c1 c2) = project' proc (if K T proc then IfThen v p c1 c2 else c1)`
              by(rw[])
           \\ qabbrev_tac `iffy = (K T):proc -> bool`
           \\ pop_assum kall_tac
           \\ pop_assum (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
           \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`s`,`v`,`p`,`c2`,`l`,`c1`,`iffy`,`pn`]
           \\ Induct
           >- (rw[preSel_def,list_trans_def,cut_ext_choice_upto_presel_nil,preSel_to_queue_def,
                  compile_network_project]
               >> qmatch_goalsub_abbrev_tac `_ (FOLDR NPar NNil a1) (FOLDR NPar NNil a2)`
               >> `a1 = a2` suffices_by simp[]
               >> unabbrev_all_tac
               >> rw[MAP_EQ_f] >> rw[]
               >> match_mp_tac project_if_l_eq
               >> conj_tac
               >- (first_x_assum drule >> fs[])
               >> conj_tac
               >- (CCONTR_TAC >> fs[])
               >> CCONTR_TAC
               >> fs[] >> rveq >> fs[preSel_def])
           \\ rpt strip_tac
           \\ `?b q c1'. c1 = Sel p b q c1'`
              by(qpat_x_assum `SUC _ = LENGTH _` mp_tac >> Cases_on `c1` >> rw[preSel_def])
           \\ rveq
           \\ `MEM q l` by(fs[preSel_def])
           \\ first_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
           \\ `p <> q` by(CCONTR_TAC >> fs[])
           \\ `project_ok q c1'`
              by(imp_res_tac compile_network_ok_project_ok
                 \\ pop_assum mp_tac \\ rpt(pop_assum kall_tac)
                 \\ rfs[project_def,split_sel_def]
                 \\ every_case_tac \\ fs[])
           \\ first_assum drule
           \\ strip_tac
           \\ qmatch_goalsub_abbrev_tac `reduction^* (FOLDR NPar NNil (MAP af _))`
           \\ qabbrev_tac `ag = \q. (NEndpoint q <|bindings := projectS q s;
                                    queue := preSel_to_queue q p (preSel p c1')|> (project' q c1'))`
           \\ `trans (af q) (LTau) (ag q)`
              by(unabbrev_all_tac >> Cases_on `iffy q`
                 >> fs[project_def,cut_ext_choice_upto_presel_def,preSel_def,
                       split_sel_def,compile_network_gen_def,preSel_to_queue_def]
                 >> rfs[]
                 >> rpt(PURE_CASE_TAC \\ fs[] \\ rveq)
                 >> simp[cut_ext_choice_upto_presel_def,SPLITP]
                 >> TRY(match_mp_tac trans_ext_choice_l_gen
                        >> fs[] >> qexists_tac `[]` >> fs[])
                 >> TRY(match_mp_tac trans_ext_choice_r_gen
                        >> fs[] >> qexists_tac `[0w]` >> qexists_tac `[]` >> fs[]))
           \\ `trans (FOLDR NPar NNil ((MAP af l1) ++ af q :: (MAP af l2)))
                     LTau (FOLDR NPar NNil ((MAP af l1) ++ ag q :: (MAP af l2)))`
                by(simp[trans_fold_par])
           \\ qabbrev_tac `iffy' = λp. if p = q then F else iffy p`
           \\ qabbrev_tac `ah = (λproc.
                       NEndpoint proc
                         <|bindings := projectS proc s;
                         queue := preSel_to_queue proc p (preSel p c1')|>
                         (project' proc (if iffy' proc then IfThen v p c1' c2 else c1')))`
           \\ match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
           \\ qexists_tac `FOLDR NPar NNil (MAP ah l)`
           \\ conj_tac
           >- (simp[reduction_def]
               \\ `MAP af l1 = MAP ah l1 /\ ag q = ah q /\ MAP af l2 = MAP ah l2`
                   suffices_by metis_tac[]
               \\ unabbrev_all_tac
               \\ rw[MAP_EQ_f]
               \\ fs[preSel_def,preSel_to_queue_def,ALL_DISTINCT_APPEND]
               \\ rpt(qpat_x_assum `trans _ _ _` kall_tac)
               \\ `proc <> p` by(CCONTR_TAC >> fs[])
               \\ `proc <> q` by(CCONTR_TAC >> fs[] >> metis_tac[])
               \\ rw[] \\ fs[project_def,split_sel_def])
           \\ first_x_assum (qspecl_then [`iffy'`,`c1'`,`l`,`c2`,`p`,`v`,`s`] mp_tac)
           \\ `project_ok p c1'` by(fs[project_def])
           \\ `compile_network_ok s c1' l` by(imp_res_tac compile_network_if_l \\ imp_res_tac compile_network_ok_dest_sel)
           \\ rpt(disch_then drule)
           \\ impl_tac
           >- (qpat_x_assum `_ = _ ++ _::_` kall_tac
               >> fs[preSel_def] >> unabbrev_all_tac >> fs[]
               >> rw[] >> rpt(first_x_assum drule) >> simp[]
               >> `proc <> p` by(CCONTR_TAC >> fs[])
               >> fs[project_def,split_sel_def]
               >> rw[])
           \\ qmatch_goalsub_abbrev_tac
                `reduction^* (FOLDR _ _ a1) (FOLDR _ _ a2) ==> reduction^* (FOLDR _ _ a3) (FOLDR _ _ a4)`
           \\ `a1 = a3 /\ a2 = a4` suffices_by metis_tac[]
           \\ unabbrev_all_tac
           \\ rw[MAP_EQ_f,cut_ext_choice_upto_presel_def,preSel_def]
           \\ `proc <> p` by(CCONTR_TAC >> fs[])
           >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
               \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
           >- (fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]
               >> rw[cut_ext_choice_upto_presel_def,SPLITP])
           >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
               \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
          ) >>
        simp[] >>
        fs[trans_s_def] >>
        match_mp_tac RTC_TRANS >>
        qexists_tac `(s,c1)` >>
        simp[] >>
        conj_tac >- metis_tac[trans_if_true] >>
        pop_assum mp_tac >>
        fs[no_self_comunication_def] >>
        qpat_x_assum `no_self_comunication c1` mp_tac >>
        rpt(pop_assum kall_tac) >>
        Induct_on `c1` >>
        fs[cut_sel_upto_def] >>
        rw[no_self_comunication_def] >>
        res_tac >>
        match_mp_tac RTC_TRANS >>
        HINT_EXISTS_TAC >> simp[] >>
        metis_tac[trans_sel]) >>
     (* If False *)
          first_x_assum(qspec_then `chor_to_endpoint$chor_size(cut_sel_upto p c2)` mp_tac) >>
     impl_tac >-
       (fs[chor_size_def] >>
        match_mp_tac LESS_EQ_LESS_TRANS >>
        qspecl_then [`p`,`c2`] assume_tac chor_size_cut_sel_upto >>
        goal_assum drule >> simp[]) >>
     disch_then(qspecl_then [`s`,`cut_sel_upto p c2`,`pn`] mp_tac) >>
     impl_tac >-
       (simp[] >>
        conj_tac >-
          (dxrule_then assume_tac compile_network_if_r >>
           fs[compile_network_ok_project_ok] >>
           rw[] >>
           res_tac >>
           match_mp_tac project_ok_cut_sel_upto >> simp[]) >>
        conj_tac >- (fs[procsOf_def,set_nub'] >> metis_tac[SUBSET_TRANS,procsOf_cut_sel_upto]) >>
        conj_tac >- (match_mp_tac no_undefined_vars_cut_sel_upto >>
                     fs[no_undefined_vars_def,free_variables_def]) >>
        match_mp_tac no_self_comunication_cut_sel_upto >>
        fs[no_self_comunication_def]) >>
     strip_tac >>
     rveq >>
     qexists_tac `s''` >>
     qexists_tac `compile_network s'' Nil pn` >>
     conj_tac >-
       (match_mp_tac(MP_CANON RTC_RTC) >> HINT_EXISTS_TAC >> simp[] >>
        qpat_x_assum `reduction^* _ _` kall_tac >>
        match_mp_tac PERM_chor_compile_network_reduction >>
        qexists_tac `p::FILTER (λy. p ≠ y) pn` >>
        conj_tac >-
          (fs[SUBSET_DEF,procsOf_def,set_nub',DISJ_IMP_THM,FORALL_AND_THM] >>
           qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
           rveq >> fs[ALL_DISTINCT_APPEND,FILTER_APPEND] >>
           fs[PERM_CONS_EQ_APPEND] >>
           qexists_tac `l1` >> qexists_tac `l2` >>
           fs[] >>
           match_mp_tac PERM_INTRO >>
           rw[APPEND_EQ_APPEND,PULL_EXISTS] >>
           disj1_tac >> qexists_tac `[]` >>
           simp[FILTER_EQ_ID] >>
           rw[EVERY_MEM] >>
           metis_tac[]) >>
        conj_tac >- (rw[MEM_FILTER,FILTER_ALL_DISTINCT]) >>
        rw[compile_network_gen_def,project_def]
        \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) pn`
                                  , `sq = <|bindings := projectS p s; queue := []|>`]
        \\ ho_match_mp_tac RTC_TRANS
        \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p c2)))
                        (compile_network s (IfThen v p c1 c2) l)`
        \\ rw [reduction_def]
        >- (ho_match_mp_tac trans_par_l
            \\ ho_match_mp_tac endpointSemTheory.trans_if_false
            \\ rw [Abbr `sq`,lookup_projectS] \\ metis_tac[lookup_projectS])
        \\ `¬MEM p l` by rw [Abbr `l`,MEM_FILTER]
        \\ `MEM p pn` by(fs[procsOf_def,SUBSET_DEF,set_nub'])
        \\ drule_then (strip_assume_tac o REWRITE_RULE [compile_network_ok_project_ok]) compile_network_if_r
        \\ first_x_assum (drule_then assume_tac)
        \\ rw [prefix_project_eq]
        \\ match_mp_tac list_trans_com_choice_l'
        \\ Q.ISPECL_THEN [`p`,`sq`,`c2`,`project' p (cut_sel_upto p c2)`]
                       mp_tac list_trans_projpre
        \\ impl_tac
        >- (CCONTR_TAC >> fs[] >> imp_res_tac MEM_presel_MEM_procsOf >>
            drule compile_network_if_r >>
            metis_tac[compile_network_ok_project_ok])
        \\ strip_tac
        \\ MAP_EVERY qexists_tac
                     [`(MAP (λ(b,q). LIntChoice p b q) (preSel p c2))`,
                      `(MAP (λ(b,q). LExtChoice p b q) (preSel p c2))`]
        \\ simp[GSYM PULL_EXISTS]
        \\ conj_tac
        >- (simp[EVERY2_MAP,ELIM_UNCURRY]
            \\ match_mp_tac EVERY2_refl \\ Cases \\ rw[])
        \\ simp[compile_network_ok_if_eq]
        \\ qexists_tac
           `FOLDR NPar NNil
             (MAP
                (λproc.
                     NEndpoint proc
                       <|bindings := projectS proc s;
                         queue := preSel_to_queue proc p (preSel p c2)|>
                       (project' proc (IfThen v p c1 c2))) l)`
        \\ imp_res_tac compile_network_if_r
        \\ simp[compile_network_cut_sel_upto]
        \\ `ALL_DISTINCT l`
           by(qunabbrev_tac `l`
              \\ match_mp_tac FILTER_ALL_DISTINCT \\ simp[])
        \\ `~MEM p (MAP SND (preSel p c2))`
             by(qhdtm_x_assum `list_trans` mp_tac
                \\ qmatch_goalsub_abbrev_tac `list_trans n1 _ n2`
                \\ rpt(pop_assum kall_tac)
                \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p`,`n1`,`n2`,`c2`]
                \\ Induct \\ rw[preSel_def,list_trans_def]
                \\ imp_res_tac sender_receiver_distinct_choice
                \\ metis_tac[])
        \\ `!x. MEM x (MAP SND(preSel p c2)) ==> MEM x l`
             by(qpat_x_assum `¬_` mp_tac \\ qpat_x_assum `¬_` mp_tac
                \\ unabbrev_all_tac\\ fs[procsOf_def,set_nub']
                \\ qpat_x_assum `set (procsOf c2) ⊆ set pn` mp_tac
                \\ rpt(pop_assum kall_tac)
                \\ simp[PULL_FORALL] \\ strip_tac \\ Induct_on `c2`
                \\ rw[preSel_def]
                \\ fs[procsOf_def,set_nub']
                \\ rw[MEM_FILTER])
        \\ conj_tac
        >- (rw[compile_network_project]
            \\ `?qf. !proc. (qf:proc ->(proc,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
            \\ `!proc qff. <|bindings := projectS proc s; queue := qff proc|>
                          = <|bindings := projectS proc s; queue := qf proc ++ qff proc|>`
                by(rw[])
            \\ pop_assum mp_tac \\ pop_assum kall_tac
            \\ disch_then (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
            \\ simp[]
            \\ pop_assum mp_tac
            \\ qhdtm_x_assum `ALL_DISTINCT` mp_tac
            \\ rpt(qpat_x_assum `¬_` mp_tac)
            \\ rename1 `MAP SND psl`
            \\ pop_assum mp_tac
            \\ rpt(pop_assum kall_tac)
            \\ rw[network_consume_LExtChoice])
        \\ `compile_network_ok s (IfThen v p c1 c2) l`
           by(fs[compile_network_ok_project_ok] >> rw[] >>
              first_x_assum match_mp_tac >> fs[Abbr `l`,MEM_FILTER])
        \\ `!proc. MEM proc l ==> project_ok proc (if K T proc then IfThen v p c1 c2 else c2)`
           by(rw[] >> fs[compile_network_ok_project_ok] >> res_tac)
        \\ rename1 `_ ⊆ set ppn`
        \\ `?pn. pn = LENGTH(preSel p c2)` by simp[]
        \\ drule_then assume_tac compile_network_if_r
        \\ simp[compile_network_cut_sel_upto]
        \\ pop_assum kall_tac
        \\ ntac 2 (pop_assum mp_tac)
        \\ dxrule compile_network_if_r
        \\ ntac 3 (pop_assum mp_tac)
        \\ qhdtm_x_assum `list_trans` kall_tac
        \\ rpt(qhdtm_x_assum `Abbrev` kall_tac)
        \\ qpat_x_assum `~MEM p l` mp_tac
        \\ qpat_x_assum `project_ok _ _` mp_tac
        \\ drule_then (assume_tac o REWRITE_RULE[compile_network_ok_project_ok]) compile_network_if_l
        \\ pop_assum drule
        \\ rpt(pop_assum kall_tac) (* ? *)
        \\ `!proc. project' proc (IfThen v p c1 c2) = project' proc (if K T proc then IfThen v p c1 c2 else c2)`
           by(rw[])
        \\ qabbrev_tac `iffy = (K T):proc -> bool`
        \\ pop_assum kall_tac
        \\ pop_assum (fn thm => Ho_Rewrite.PURE_ONCE_REWRITE_TAC [thm])
        \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`s`,`v`,`p`,`c2`,`l`,`c1`,`iffy`,`pn`]
        \\ Induct
        >- (rw[preSel_def,list_trans_def,cut_ext_choice_upto_presel_nil,preSel_to_queue_def,
               compile_network_project]
            >> qmatch_goalsub_abbrev_tac `_ (FOLDR NPar NNil a1) (FOLDR NPar NNil a2)`
            >> `a1 = a2` suffices_by simp[]
            >> unabbrev_all_tac
            >> rw[MAP_EQ_f] >> rw[]
            >> match_mp_tac project_if_r_eq
            >> conj_tac
            >- (first_x_assum drule >> fs[])
            >> conj_tac
            >- (CCONTR_TAC >> fs[])
            >> CCONTR_TAC
            >> fs[] >> rveq >> fs[preSel_def])
        \\ rpt strip_tac
        \\ `?b q c2'. c2 = Sel p b q c2'`
           by(qpat_x_assum `SUC _ = LENGTH _` mp_tac >> Cases_on `c2` >> rw[preSel_def])
        \\ rveq
        \\ `MEM q l` by(fs[preSel_def])
        \\ first_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
        \\ `p <> q` by(CCONTR_TAC >> fs[])
        \\ `project_ok q c2'`
           by(imp_res_tac compile_network_ok_project_ok
              \\ pop_assum mp_tac \\ rpt(pop_assum kall_tac)
              \\ rfs[project_def,split_sel_def]
              \\ every_case_tac \\ fs[])
        \\ first_assum drule
        \\ strip_tac
        \\ qmatch_goalsub_abbrev_tac `reduction^* (FOLDR NPar NNil (MAP af _))`
        \\ qabbrev_tac `ag = \q. (NEndpoint q <|bindings := projectS q s;
                                 queue := preSel_to_queue q p (preSel p c2')|> (project' q c2'))`
        \\ `trans (af q) (LTau) (ag q)`
           by(unabbrev_all_tac >> Cases_on `iffy q`
              >> fs[project_def,cut_ext_choice_upto_presel_def,preSel_def,
                    split_sel_def,compile_network_gen_def,preSel_to_queue_def]
              >> rfs[]
              >> rpt(PURE_CASE_TAC \\ fs[] \\ rveq)
              >> simp[cut_ext_choice_upto_presel_def,SPLITP]
              >> TRY(match_mp_tac trans_ext_choice_l_gen
                     >> fs[] >> qexists_tac `[]` >> fs[])
              >> TRY(match_mp_tac trans_ext_choice_r_gen
                     >> fs[] >> qexists_tac `[0w]` >> qexists_tac `[]` >> fs[]))
        \\ `trans (FOLDR NPar NNil ((MAP af l1) ++ af q :: (MAP af l2)))
                  LTau (FOLDR NPar NNil ((MAP af l1) ++ ag q :: (MAP af l2)))`
             by(simp[trans_fold_par])
        \\ qabbrev_tac `iffy' = λp. if p = q then F else iffy p`
        \\ qabbrev_tac `ah = (λproc.
                    NEndpoint proc
                      <|bindings := projectS proc s;
                      queue := preSel_to_queue proc p (preSel p c2')|>
                      (project' proc (if iffy' proc then IfThen v p c1 c2' else c2')))`
        \\ match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES))
        \\ qexists_tac `FOLDR NPar NNil (MAP ah l)`
        \\ conj_tac
        >- (simp[reduction_def]
            \\ `MAP af l1 = MAP ah l1 /\ ag q = ah q /\ MAP af l2 = MAP ah l2`
                suffices_by metis_tac[]
            \\ unabbrev_all_tac
            \\ rw[MAP_EQ_f]
            \\ fs[preSel_def,preSel_to_queue_def,ALL_DISTINCT_APPEND]
            \\ rpt(qpat_x_assum `trans _ _ _` kall_tac)
            \\ `proc <> p` by(CCONTR_TAC >> fs[])
            \\ `proc <> q` by(CCONTR_TAC >> fs[] >> metis_tac[])
            \\ rw[] \\ fs[project_def,split_sel_def])
        \\ first_x_assum (qspecl_then [`iffy'`,`c1`,`l`,`c2'`,`p`,`v`,`s`] mp_tac)
        \\ `project_ok p c2'` by(fs[project_def])
        \\ `compile_network_ok s c2' l` by(imp_res_tac compile_network_if_r \\ imp_res_tac compile_network_ok_dest_sel)
        \\ rpt(disch_then drule)
        \\ impl_tac
        >- (qpat_x_assum `_ = _ ++ _::_` kall_tac
            >> fs[preSel_def] >> unabbrev_all_tac >> fs[]
            >> rw[] >> rpt(first_x_assum drule) >> simp[]
            >> `proc <> p` by(CCONTR_TAC >> fs[])
            >> fs[project_def,split_sel_def]
            >> rw[])
        \\ qmatch_goalsub_abbrev_tac
             `reduction^* (FOLDR _ _ a1) (FOLDR _ _ a2) ==> reduction^* (FOLDR _ _ a3) (FOLDR _ _ a4)`
        \\ `a1 = a3 /\ a2 = a4` suffices_by metis_tac[]
        \\ unabbrev_all_tac
        \\ rw[MAP_EQ_f,cut_ext_choice_upto_presel_def,preSel_def]
        \\ `proc <> p` by(CCONTR_TAC >> fs[])
        >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
            \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
        >- (fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]
            >> rw[cut_ext_choice_upto_presel_def,SPLITP])
        >- (`proc <> q` by(CCONTR_TAC >> fs[ALL_DISTINCT_APPEND] >> metis_tac[])
            \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons])
       ) >>
     simp[] >>
     fs[trans_s_def] >>
     match_mp_tac RTC_TRANS >>
     qexists_tac `(s,c2)` >>
     simp[] >>
     conj_tac >- metis_tac[trans_if_false] >>
     pop_assum mp_tac >>
     fs[no_self_comunication_def] >>
     qpat_x_assum `no_self_comunication c2` mp_tac >>
     rpt(pop_assum kall_tac) >>
     Induct_on `c2` >>
     fs[cut_sel_upto_def] >>
     rw[no_self_comunication_def] >>
     res_tac >>
     match_mp_tac RTC_TRANS >>
     HINT_EXISTS_TAC >> simp[] >>
     metis_tac[trans_sel]) >-
    ((* Com *)
     rename1 `Com p vp q vq c` >>
     `?d. FLOOKUP s (vp,p) = SOME d`
       by(fs[no_undefined_vars_def,free_variables_def] >>
          imp_res_tac FDOM_FLOOKUP >> goal_assum drule) >>
     first_x_assum(qspec_then `chor_to_endpoint$chor_size c` mp_tac) >>
     impl_tac >- fs[chor_size_def] >>
     disch_then(qspecl_then [`s |+ ((vq,q),d)`,`c`] mp_tac) >>
     fs[] >>
     drule_then(qspec_then `d` assume_tac) compile_network_ok_dest_com >>
     disch_then drule >>
     impl_tac >-
       (fs[no_self_comunication_def,procsOf_def,no_undefined_vars_def,free_variables_def,
           set_nub',SUBSET_DEF,DELETE_DEF] >> metis_tac[]) >>
     strip_tac >>
     qexists_tac `s''` >>
     conj_tac >-
       (match_mp_tac (MP_CANON RTC_RTC) >>
        HINT_EXISTS_TAC >> simp[] >>
        match_mp_tac chor_compile_network_COM' >>
        fs[procsOf_def,set_nub',no_self_comunication_def] >>
        fs[compile_network_gen_def,project_def] >>
        match_mp_tac RTC_TRANS >>
        qexists_tac `
              (NPar
                 (NEndpoint p <|bindings := projectS p s; queue := []|>
                    (project' p c))
                 (NPar
                    (NEndpoint q <|bindings := projectS q s; queue := [(p,d)]|>
                       (Receive p vq (project' q c)))
                    (compile_network s c
                       (FILTER (λx. p ≠ x ∧ q ≠ x) pn))))` >>
        conj_tac >-
          (simp[reduction_def] >>
           match_mp_tac trans_com_l >>
           goal_assum drule >>
           qexists_tac `d` >>
           conj_tac >-
             (simp[fupdate_projectS] >>
              match_mp_tac trans_send >> simp[lookup_projectS]) >>
           simp[cn_ignore_state_update,MEM_FILTER,cn_ignore_com] >>
           match_mp_tac trans_par_l >>
           drule_then(qspecl_then [`<|bindings := projectS q s; queue := []|>`,`d`,
                              `Receive p vq (project' q c)`] assume_tac) trans_enqueue >>
           fs[]) >>
        match_mp_tac RTC_SUBSET >>
        simp[reduction_def] >>
        simp[fupdate_projectS] >>
        simp[cn_ignore_state_update,MEM_FILTER,cn_ignore_com] >>
        match_mp_tac trans_par_r >>
        match_mp_tac trans_par_l >>
        match_mp_tac trans_dequeue_gen >>
        simp[projectS_fupdate]) >>
     fs[trans_s_def] >>
     match_mp_tac RTC_TRANS >>
     HINT_EXISTS_TAC >> simp[] >>
     fs[no_self_comunication_def] >>
     metis_tac[trans_com]) >-
    (rename1 `Let v p f vl c` >>
     `EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))`
       by(fs[no_undefined_vars_def,free_variables_def] >>
          rw[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
          fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,procsOf_def,set_nub'] >>
          metis_tac[IS_SOME_EXISTS,FDOM_FLOOKUP]) >>
     first_x_assum(qspec_then `chor_to_endpoint$chor_size c` mp_tac) >>
     impl_tac >- fs[chor_size_def] >>
     disch_then(qspecl_then [`s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl)))`,`c`] mp_tac) >>
     fs[] >>
     disch_then(qspec_then `pn` mp_tac) >>
     impl_tac >-
       (reverse conj_tac >-
          (fs[no_undefined_vars_def,procsOf_def,no_self_comunication_def] >>
           fs[SUBSET_DEF,set_nub',free_variables_def] >> metis_tac[]) >>
        fs[compile_network_ok_project_ok] >>
        rw[] >> res_tac >>
        fs[project_def] >> every_case_tac >> fs[]) >>
     strip_tac >>
     qexists_tac `s''` >>
     conj_tac >-
       (match_mp_tac RTC_TRANS >>
        HINT_EXISTS_TAC >> simp[] >>
        fs[procsOf_def,set_nub'] >>
        qhdtm_x_assum `EVERY` mp_tac >>
        qhdtm_x_assum `ALL_DISTINCT` mp_tac >>
        qpat_x_assum `MEM _ _` mp_tac >>
        rpt(pop_assum kall_tac) >>
        ntac 2 strip_tac >>
        fs[MEM_SPLIT] >> rveq >> fs[ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM] >>
        rpt(qpat_x_assum `~MEM _ _` mp_tac) >>
        rpt(pop_assum kall_tac) >>
        MAP_EVERY qid_spec_tac [`p`,`l1`,`l2`,`s`,`vl`,`v`,`c`,`f`] >>
        Induct_on `l1` >-
          (rw[compile_network_gen_def,project_def,reduction_def] >>
           fs[cn_ignore_let,cn_ignore_state_update] >>
           match_mp_tac trans_par_l >>
           match_mp_tac trans_let_gen >>
           simp[] >>
           rw []
           >- (Induct_on `vl` \\ rw [lookup_projectS'])
           >- (rw [projectS_fupdate] >> rpt AP_TERM_TAC
               \\ Induct_on `vl` >> rw [lookup_projectS'])) >-
          (rw[compile_network_gen_def,project_def,reduction_def] >>
           fs[cn_ignore_let,cn_ignore_state_update] >>
           simp[projectS_fupdate,projectS_fupdate_fresh] >>
           match_mp_tac trans_par_r >>
           fs[reduction_def])) >>
     fs[trans_s_def] >>
     match_mp_tac RTC_TRANS >>
     HINT_EXISTS_TAC >> simp[] >>
     metis_tac[trans_let]) >-
    (rename1 `Sel p b q c` >>
     first_x_assum(qspec_then `chor_to_endpoint$chor_size c` mp_tac) >>
     impl_tac >- fs[chor_size_def] >>
     disch_then(qspecl_then [`s`,`c`] mp_tac) >>
     fs[] >>
     drule_then assume_tac compile_network_ok_dest_sel >>
     disch_then drule >>
     impl_tac >-
       (fs[no_self_comunication_def,procsOf_def,no_undefined_vars_def,free_variables_def,
           set_nub',SUBSET_DEF,DELETE_DEF] >> metis_tac[]) >>
     strip_tac >>
     qexists_tac `s''` >>
     conj_tac >-
       (match_mp_tac (MP_CANON RTC_RTC) >>
        HINT_EXISTS_TAC >> simp[] >>
        match_mp_tac chor_compile_network_Sel' >>
        fs[procsOf_def,set_nub',no_self_comunication_def] >>
        fs[compile_network_gen_def,project_def] >>
        match_mp_tac RTC_TRANS >>
        qmatch_goalsub_abbrev_tac `(NPar _ (NPar (NEndpoint _ _ a1) _))` >>
        qexists_tac `
              (NPar
                 (NEndpoint p <|bindings := projectS p s; queue := []|>
                    (project' p c))
                 (NPar
                    (NEndpoint q <|bindings := projectS q s; queue := [(p,if b then [1w] else [0w])]|>
                       a1)
                    (compile_network s c
                       (FILTER (λx. p ≠ x ∧ q ≠ x) pn))))` >>
        qunabbrev_tac `a1` >>
        conj_tac >-
          (simp[reduction_def] >>
           match_mp_tac trans_com_choice_l >>
           goal_assum drule >>
           qexists_tac `b` >>
           conj_tac >-
             (simp[fupdate_projectS] >>
              match_mp_tac trans_int_choice >> simp[]) >>
           simp[cn_ignore_state_update,MEM_FILTER,cn_ignore_sel] >>
           match_mp_tac trans_par_l >>
           rw[] >-
             (drule_then(qspecl_then [`<|bindings := projectS q s; queue := []|>`] assume_tac) trans_enqueue_choice_l >>
              fs[]) >>
           drule_then(qspecl_then [`<|bindings := projectS q s; queue := []|>`] assume_tac) trans_enqueue_choice_r >>
           fs[]) >>
        match_mp_tac RTC_SUBSET >>
        simp[reduction_def] >>
        simp[fupdate_projectS] >>
        simp[cn_ignore_state_update,MEM_FILTER,cn_ignore_sel] >>
        match_mp_tac trans_par_r >>
        match_mp_tac trans_par_l >>
        rw[] >- (match_mp_tac trans_ext_choice_l_gen >> rw[]) >>
        match_mp_tac trans_ext_choice_r_gen >> rw[]) >>
     fs[trans_s_def] >>
     match_mp_tac RTC_TRANS >>
     HINT_EXISTS_TAC >> simp[] >>
     fs[no_self_comunication_def] >>
     metis_tac[trans_sel])
QED

Theorem reduction_list_trans:
  reduction^* p1 p2 ==>
  ?n. list_trans p1 (REPLICATE n LTau) p2
Proof
  rw[RTC_eq_NRC] >>
  qexists_tac `n` >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`p1`,`p2`] >>
  Induct_on `n` >>
  rw[list_trans_def,NRC,reduction_def] >>
  res_tac >> goal_assum drule >> rw[]
QED

Theorem list_trans_reduction:
  !n p1 p2.
  list_trans p1 (REPLICATE n LTau) p2 ==>
  reduction^* p1 p2
Proof
  Induct >>
  rw[list_trans_def] >>
  match_mp_tac RTC_TRANS >>
  simp[reduction_def] >>
  res_tac >> goal_assum drule >>
  simp[]
QED

Theorem trans_Send_compile_network_Nil:
  !ps s'' alpha p1 p2 d p3.
  trans (compile_network s'' Nil ps) (LSend p2 d p3) p1 ==> F
Proof
  Induct >>
  rw[compile_network_gen_def,project_def] >-
    (spose_not_then strip_assume_tac >>
     fs[Once endpointSemTheory.trans_cases]) >>
  spose_not_then (strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >>
  rveq >>
  rfs[] >>
  pop_assum(strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >> rveq
QED

Theorem trans_IntChoice_compile_network_Nil:
  !ps s'' alpha p1 p2 b p3.
  trans (compile_network s'' Nil ps) (LIntChoice p2 b p3) p1 ==> F
Proof
  Induct >>
  rw[compile_network_gen_def,project_def] >-
    (spose_not_then strip_assume_tac >>
     fs[Once endpointSemTheory.trans_cases]) >>
  spose_not_then (strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >>
  rveq >>
  rfs[] >>
  pop_assum(strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >> rveq
QED

Theorem trans_compile_network_Nil:
  !ps s'' alpha p1.
  trans (compile_network s'' Nil ps) LTau p1 ==> F
Proof
  Induct >>
  rw[compile_network_gen_def,project_def] >-
    (spose_not_then strip_assume_tac >>
     fs[Once endpointSemTheory.trans_cases]) >>
  spose_not_then (strip_assume_tac o REWRITE_RULE[Once endpointSemTheory.trans_cases]) >>
  fs[] >>
  rveq >>
  rfs[] >>
  imp_res_tac trans_Send_compile_network_Nil >> imp_res_tac trans_IntChoice_compile_network_Nil >> fs[] >>
  qpat_x_assum ` trans (NEndpoint _ _ _) _ _` (strip_assume_tac o ONCE_REWRITE_RULE[endpointSemTheory.trans_cases]) >>
  fs[] >> rveq
QED

Theorem reduction_compile_network_Nil:
  !s'' ps p1.
  reduction^* (compile_network s'' Nil ps) p1 ==> p1 = compile_network s'' Nil ps
Proof
  rw[Once RTC_cases,reduction_def] >>
  imp_res_tac trans_compile_network_Nil
QED

Theorem compile_network_reflection:
   ∀s c p2.
    compile_network_ok s c (procsOf c)
    ∧ reduction^* (compile_network s c (procsOf c)) p2
    ∧ no_undefined_vars (s,c)
    ==> ∃s'' c'' p3.
              reduction^* p2 p3
              ∧ trans_s (s,c) (s'',c'')
              ∧ qcong p3 (compile_network s'' c'' (procsOf c))
Proof
  rw[] >>
  imp_res_tac compile_network_ok_no_self_comunication >>
  drule compile_network_reflection_lemma >>
  simp[procsOf_all_distinct] >>
  strip_tac >>
  qexists_tac `s''` >>
  qexists_tac `Nil` >>
  simp[] >>
  rpt(dxrule_then strip_assume_tac reduction_list_trans) >>
  drule endpoint_confluence_weak_contract >>
  qpat_x_assum `list_trans _ _ (compile_network _ _ _)` assume_tac >>
  disch_then drule >>
  impl_tac >- simp[FST_endpoints_compile_network,procsOf_all_distinct] >>
  strip_tac >>
  rpt(dxrule_then strip_assume_tac list_trans_reduction) >>
  goal_assum drule >>
  imp_res_tac reduction_compile_network_Nil >>
  rveq >>
  simp[]
QED


Theorem trans_s_nil:
  trans_s (s,Nil) sc ==> sc = (s,Nil)
Proof
  rw[trans_s_def,Once RTC_cases] >>
  fs[Once trans_cases]
QED

Theorem compile_network_preservation:
   ∀s c s'' c''.
    compile_network_ok s c (procsOf c)
    ∧ trans_s (s,c) (s'',c'')
    ∧ no_undefined_vars (s,c)
    ==> ∃s''' c''' p2.
              reduction^* (compile_network s c (procsOf c)) p2
              ∧ trans_s (s'',c'') (s''',c''')
              /\ p2 = (compile_network s''' c''' (procsOf c))
Proof
  rw []
  \\ imp_res_tac compile_network_ok_no_self_comunication
  \\ drule_all trans_s_ln
  \\ rw []
  \\ drule_all compile_network_preservation_trans_ln
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ irule trans_s_trans_s
  \\ IMP_RES_TAC trans_ln_IMP_trans_s
  \\ asm_exists_tac \\ fs []
QED

val _ = export_theory ()
