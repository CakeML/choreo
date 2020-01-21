open preamble endpointLangTheory bakery_to_endpointTheory
              endpointSemanticsTheory endpointPropsTheory
              endpointCongTheory semBakeryTheory;

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
  \\ TRY (Cases_on `p = l0`)
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

Theorem conf_trans:
  ∀epn epn' epn''.
   ALL_DISTINCT (MAP FST (endpoints epn))
   ⇒ epn ≅< epn' ∧ epn' ≅< epn'' ⇒ epn ≅< epn''
Proof
  rw [epn_conf_def]
  \\ drule
  \\ cheat (* TODO *)
QED

val compile_network_preservation = Q.store_thm("compile_network_preservation",
  `∀s c α τ s' c'. compile_network_ok s c (procsOf c)
    ∧ trans (s,c) (α,τ) (s',c')
    ⇒ ∃s'' c''. trans_s (s',c') (s'',c'')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'' c'' (procsOf c))`,
  `∀s c α τ s' c'. trans (s,c) (α,τ) (s',c')
    ⇒ (compile_network_ok s c (procsOf c)
    ⇒ ∃s'' c''. trans_s (s',c') (s'',c'')
       ∧ reduction^* (compile_network s   c   (procsOf c))
                     (compile_network s'' c'' (procsOf c)))`
  suffices_by metis_tac []
  \\ ho_match_mp_tac trans_pairind
  \\ rw [ compile_network_gen_def
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
     \\ pop_assum (K ALL_TAC)
     \\ rw []
     >- (Induct_on `vl` \\ rw [lookup_projectS'])
     >- (rw [projectS_fupdate] >> rpt AP_TERM_TAC
        \\ Induct_on `vl` >> rw [lookup_projectS']))
  (* If true *)
  >- (MAP_EVERY Q.EXISTS_TAC [`s`,`cut_sel_upto p c'`]
     \\ rw []
     >- (pop_assum (K ALL_TAC) >> pop_assum (K ALL_TAC)
        \\ Induct_on `c'` >> rw [trans_s_def,cut_sel_upto_def]
        \\ Cases_on `l0 = l` >> fs [project_def]
        \\ ho_match_mp_tac RTC_TRANS
        \\  metis_tac [trans_s_def,trans_sel])
     \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) (nub' (procsOf c' ⧺ procsOf c2))`
                               , `sq = <|bindings := projectS p s; queue := []|>`
                               ]
     \\ ho_match_mp_tac RTC_TRANS
     \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p c')))
                           (compile_network s (IfThen v p c' c2) l)`
     \\ rw [reduction_def]
     >- (ho_match_mp_tac trans_par_l
        \\ ho_match_mp_tac endpointSemanticsTheory.trans_if_true
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
     >- (`?qf. !proc. (qf:datum ->(datum,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
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
     \\ qabbrev_tac `iffy = (K T):datum -> bool`
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
         \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]))
  (* If false *)
  >- (MAP_EVERY Q.EXISTS_TAC [`s`,`cut_sel_upto p c'`]
     \\ rw []
     >- (pop_assum (K ALL_TAC)
        \\ Induct_on `c'` >> rw [trans_s_def,cut_sel_upto_def]
        \\ Cases_on `l0 = l` >> fs [project_def]
        \\ ho_match_mp_tac RTC_TRANS
        \\  metis_tac [trans_s_def,trans_sel])
     \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p ≠ y) (nub' (procsOf c1 ⧺ procsOf c'))`
                               , `sq = <|bindings := projectS p s; queue := []|>`
                               ]
     \\ ho_match_mp_tac RTC_TRANS
     \\ Q.EXISTS_TAC `NPar (NEndpoint p sq (SND (project p c')))
                           (compile_network s (IfThen v p c1 c') l)`
     \\ rw [reduction_def]
     >- (ho_match_mp_tac trans_par_l
        \\ ho_match_mp_tac endpointSemanticsTheory.trans_if_false
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
     >- (`?qf. !proc. (qf:datum ->(datum,datum) alist) proc = []` by(qexists_tac `K []` \\ rw[])
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
     \\ qabbrev_tac `iffy = (K T):datum -> bool`
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
         \\ fs[project_def,cut_ext_choice_upto_presel_def,cut_ext_choice_upto_presel_cons]))

  \\ cheat (* TODO *)
);

val _ = export_theory ()
