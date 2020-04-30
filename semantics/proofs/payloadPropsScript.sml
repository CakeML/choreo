open preamble payloadSemTheory payloadLangTheory choreoUtilsTheory;

val _ = new_theory "payloadProps";

Theorem normalise_queues_idem[simp]:
  normalise_queues(normalise_queues q) = normalise_queues q
Proof
  rw[normalise_queues_def,fmap_eq_flookup,FLOOKUP_DRESTRICT]
QED

Theorem normalised_normalise_queues[simp]:
  normalised(normalise_queues q)
Proof
  rw[normalised_def]
QED

Theorem qlk_normalise_queues[simp]:
  qlk (normalise_queues q) p = qlk q p
Proof
  rw[normalise_queues_def,qlk_def,fget_def,FLOOKUP_DRESTRICT] >> rw[]
QED

Theorem normalise_queues_qpush[simp]:
  normalise_queues (qpush q p d) = qpush (normalise_queues q) p d
Proof
  rw[normalise_queues_def,qlk_def,fget_def,FLOOKUP_DRESTRICT,qpush_def,fmap_eq_flookup,
     FLOOKUP_UPDATE]
QED

Theorem DRESTRICT_normalise_queues:
  normalise_queues (DRESTRICT q f) = DRESTRICT (normalise_queues q) f
Proof
  rw[normalise_queues_def,fmap_eq_flookup,FLOOKUP_DRESTRICT] >> rw[] >> fs[]
QED

Theorem normalised_qpush[simp]:
  normalised q ⇒ normalised(qpush q p d)
Proof
  rw[normalised_def]
QED

Theorem qlk_update[simp]:
  qlk (q |+ (p,x)) p = x
Proof
  EVAL_TAC
QED

Theorem qlk_update2[simp]:
  p1 ≠ p2 ⇒ qlk (q |+ (p1,x)) p2 = qlk q p2
Proof
  EVAL_TAC >> rw[]
QED

Theorem qlk_FEMPTY[simp]:
  qlk FEMPTY p = []
Proof
  EVAL_TAC
QED

Theorem normalise_queues_FUPDATE_NONEMPTY:
  normalise_queues(q |+ (p,l)) =
  (if l = [] then
     normalise_queues (DRESTRICT q (COMPL {p}))
   else
     normalise_queues q |+ (p,l))
Proof
  rw[normalise_queues_def,fmap_eq_flookup,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >>
  rw[] >> fs[] >> fs[] >> every_case_tac >> fs[]
QED

Theorem FLOOKUP_normalise_queues_FUPDATE:
  FLOOKUP(normalise_queues(q |+ (p1,l))) p2 =
  if p1 = p2 then
    if l = [] then
      NONE
    else
      SOME l
  else
    FLOOKUP(normalise_queues q) p2
Proof
  rw[normalise_queues_def,fmap_eq_flookup,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
QED

Theorem FLOOKUP_normalise_queues:
  FLOOKUP (normalise_queues q) p =
  case FLOOKUP q p of
    NONE => NONE
  | SOME l => if l = [] then NONE else SOME l
Proof
  rw[normalise_queues_def,fmap_eq_flookup,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >>
  TOP_CASE_TAC >> fs[]
QED

Theorem payload_trans_normalised:
  ∀conf p1 alpha p2.
  trans conf p1 alpha p2 ∧ normalised_network p1 ⇒ normalised_network p2
Proof
  simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_ind >>
  rw[normalised_network_def]
QED

Theorem payload_reduction_normalised:
  ∀conf p1 alpha p2.
  (reduction conf)^* p1 p2 ∧ normalised_network p1 ⇒ normalised_network p2
Proof
  rw [] \\ rpt (pop_assum mp_tac)
  \\ map_every qid_spec_tac [‘p2’,‘p1’]
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rw [] \\ metis_tac [payload_trans_normalised,reduction_def]
QED

(* todo: move? *)
val EXISTS_REPLICATE = Q.store_thm("EXISTS_REPLICATE",
  `!f n d. EXISTS f (REPLICATE n d) = (n > 0 /\ f d)`,
  Induct_on `n` >> rw[EQ_IMP_THM]);

val unpad_pad = Q.store_thm("unpad_pad",
  `!conf d. unpad(pad conf d) = TAKE conf.payload_size d`,
  rw[pad_def,unpad_def,SPLITP_APPEND,EXISTS_REPLICATE,SPLITP]
  >> TRY(first_x_assum(assume_tac o GSYM)
         >> rw[TAKE_LENGTH_ID] >> NO_TAC)
  >> imp_res_tac LESS_IMP_LESS_OR_EQ
  >> rw[TAKE_LENGTH_TOO_LONG]);

val pad_LENGTH = Q.store_thm("pad_LENGTH",
  `!conf d. LENGTH(pad conf d) = conf.payload_size + 1`,
  rw[pad_def]);

val unpad_pad_LENGTH = Q.store_thm("unpad_pad_LENGTH",
  `!conf d. LENGTH(unpad(pad conf d)) <= conf.payload_size`,
  rw[unpad_pad,LENGTH_TAKE_EQ]);

val final_pad_LENGTH = Q.store_thm("final_pad_LENGTH",
  `!conf d. final(pad conf d) <=> LENGTH d <= conf.payload_size`,
  rw[pad_def,final_def])

val final_pad_TAKE = Q.store_thm("final_pad_TAKE",
  `!conf d. final(pad conf d) ==> TAKE conf.payload_size d = d`,
  metis_tac[final_pad_LENGTH,TAKE_LENGTH_TOO_LONG])

val intermediate_pad_LENGTH = Q.store_thm("intermediate_pad_LENGTH",
  `!conf d. intermediate(pad conf d) <=> conf.payload_size < LENGTH d`,
  rw[pad_def,intermediate_def])

val pad_not_final = Q.store_thm("pad_not_final",
  `!conf d. ¬final (pad conf d) <=> intermediate(pad conf d)`,
  rw[final_def,pad_def,intermediate_def]);

val pad_not_intermediate = Q.store_thm("pad_not_intermediate",
  `!conf d. ¬intermediate (pad conf d) <=> final(pad conf d)`,
  metis_tac[pad_not_final]);

val trans_enqueue' = Q.store_thm("trans_enqueue'",
  `∀conf s d p1 p2 e q.
     p1 ≠ p2
     ⇒ trans conf (NEndpoint p2 (s with queues := q) e) (LReceive p1 d p2)
       (NEndpoint p2 (s with queues := qpush q p1 d) e)`,
  rpt strip_tac
  >> `s with queues := qpush q p1 d = (s with queues := q) with queues := qpush ((s with queues := q).queues) p1 d` by fs[]
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> match_mp_tac trans_enqueue
  >> simp[]);

Theorem qlk_qpush[simp]:
  qlk (qpush q p1 d) p1 = qlk q p1 ++ [d]
Proof
  rw[qlk_def,qpush_def,fget_def,FLOOKUP_UPDATE]
QED

Theorem normalise_queues_FUPDATE_FUPDATE[simp]:
  normalise_queues(q |+ (p,d)) |+ (p,d') = normalise_queues q |+ (p,d')
Proof
  rw[fmap_eq_flookup,normalise_queues_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
QED

Theorem trans_dequeue_last_payload':
  ∀conf s1 s2 v p1 p2 e d tl ds q.
     p1 ≠ p2 ∧ qlk s1.queues p1 = d::tl ∧ final d ∧
     s2.bindings = s1.bindings |+ (v,FLAT (SNOC (unpad d) ds)) ∧
     s2.queues = normalise_queues(s1.queues |+ (p1,tl))
     ⇒
     trans conf (NEndpoint p2 s1 (Receive p1 v ds e)) LTau
       (NEndpoint p2 s2 e)
Proof
  rpt strip_tac >>
  drule trans_dequeue_last_payload >>
  rpt(disch_then drule) >>
  fs[] >>
  disch_then(qspecl_then [‘conf’,‘v’,‘e’,‘ds’] mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘trans _ _ _ (NEndpoint _ a1 _)’ >>
  ‘a1 = s2’ suffices_by simp[] >>
  rw[Abbr ‘a1’,state_component_equality]
QED

Theorem trans_dequeue_intermediate_payload':
  ∀conf s1 s2 v p1 p2 e d ds tl.
     p1 ≠ p2 ∧ qlk s1.queues p1 = d::tl ∧ intermediate d ∧
     s2.bindings = s1.bindings ∧
     s2.queues = normalise_queues(s1.queues |+ (p1,tl))
      ⇒
     trans conf (NEndpoint p2 s1 (Receive p1 v ds e)) LTau
       (NEndpoint p2 s2
          (Receive p1 v (SNOC (unpad d) ds) e))
Proof
  rpt strip_tac >>
  drule trans_dequeue_intermediate_payload >>
  rpt(disch_then drule) >>
  fs[] >>
  disch_then(qspecl_then [‘conf’,‘v’,‘e’,‘ds’] mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘trans _ _ _ (NEndpoint _ a1 _)’ >>
  ‘a1 = s2’ suffices_by simp[] >>
  rw[Abbr ‘a1’,state_component_equality]
QED

val trans_let' = Q.store_thm("trans_let'",
  `∀conf s v p f vl e q.
         EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl) ⇒
         trans conf (NEndpoint p (s with queues:= q) (Let v f vl e)) LTau
           (NEndpoint p
              (<|bindings := s.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s.bindings) vl));
                 queues:= q
                 |>) e)`,
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `trans _ (NEndpoint _ s1 _) _ (NEndpoint _ s2 _)`
  >> `s2 = s1 with bindings := s1.bindings |+ (v,f (MAP (THE ∘ FLOOKUP s1.bindings) vl))`
     by(unabbrev_all_tac >> simp[])
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
  >> unabbrev_all_tac
  >> match_mp_tac trans_let
  >> simp[]);

val trans_IMP_weak_trans = Q.store_thm("trans_IMP_weak_trans",
  `∀conf p alpha q. trans conf p alpha q ==> weak_trans conf p alpha q`,
  rw[weak_trans_def,weak_tau_trans_def]
  >> metis_tac[RTC_REFL,RTC_SINGLE,reduction_def]);

val reduction_par_l = Q.store_thm("reduction_par_l",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar p r) (NPar q r)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_l]);

val reduction_par_r = Q.store_thm("reduction_par_r",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar r p) (NPar r q)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_r]);

val trans_nil_false = Q.store_thm("trans_nil_false",
  `∀conf alpha n. trans conf NNil alpha n = F`,
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[trans_cases]
  >> fs[]);

val reduction_nil = Q.store_thm("reduction_nil",
  `∀conf n. (reduction conf)^* NNil n ==> n = NNil`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = NNil`
  >> pop_assum (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> simp[]
  >> rpt(last_x_assum mp_tac)
  >> PURE_ONCE_REWRITE_TAC [AND_IMP_INTRO]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n`,`a1`]
  >> ho_match_mp_tac RTC_lifts_invariants
  >> simp[payloadSemTheory.reduction_def,trans_nil_false]);

val reduction_par_l = Q.store_thm("reduction_par_l",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar p r) (NPar q r)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_l]);

val reduction_par_r = Q.store_thm("reduction_par_r",
  `∀p q r conf. (reduction conf)^* p q ==> (reduction conf)^* (NPar r p) (NPar r q)`,
  rpt gen_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q`,`p`]
  >> ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- simp[RTC_REFL]
  >> match_mp_tac (RTC_RULES |> SPEC_ALL |> CONJUNCT2)
  >> metis_tac[reduction_def,trans_par_r]);

val trans_nil_false = Q.store_thm("trans_nil_false",
  `∀conf alpha n. trans conf NNil alpha n = F`,
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[trans_cases]
  >> fs[]);

val reduction_nil = Q.store_thm("reduction_nil",
  `∀conf n. (reduction conf)^* NNil n ==> n = NNil`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = NNil`
  >> pop_assum (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> simp[]
  >> rpt(last_x_assum mp_tac)
  >> PURE_ONCE_REWRITE_TAC [AND_IMP_INTRO]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`n`,`a1`]
  >> ho_match_mp_tac RTC_lifts_invariants
  >> simp[payloadSemTheory.reduction_def,trans_nil_false]);

val list_trans_def = Define `
    (list_trans conf p [] q = (p = q))
 /\ (list_trans conf p (alpha::l) q = ?p'. trans conf p alpha p' /\ list_trans conf p' l q)`

val list_trans_append = Q.store_thm("list_trans_append",
  `!l1 n1 l2 n2 conf. list_trans conf n1 (l1 ++ l2) n2 =
  ?n3. list_trans conf n1 l1 n3 /\ list_trans conf n3 l2 n2`,
  Induct_on `l1` >> rpt strip_tac >> fs[list_trans_def]
  >> rw[EQ_IMP_THM] >> fs[] >> metis_tac[]);

val list_trans_par_l = Q.store_thm("list_trans_par_l",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar p r) alpha (NPar q r)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemTheory.trans_par_l]);

val list_trans_par_r = Q.store_thm("list_trans_par_r",
  `∀conf p alpha q r. list_trans conf p alpha q ==> list_trans conf (NPar r p) alpha (NPar r q)`,
  Induct_on `alpha`
  >- simp[list_trans_def]
  >> rpt strip_tac
  >> fs[list_trans_def] >> metis_tac[payloadSemTheory.trans_par_r]);

val endpoint_names_trans = Q.store_thm("endpoint_names_trans",
  `!conf n1 alpha n2. trans conf n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  ho_match_mp_tac trans_strongind >> rpt strip_tac >> fs[endpoints_def]);

val endpoint_names_list_trans = Q.store_thm("endpoint_names_list_trans",
  `!conf n1 alpha n2. list_trans conf n1 alpha n2 ==> MAP FST (endpoints n2) = MAP FST(endpoints n1)`,
  Induct_on `alpha` >> rw[list_trans_def] >>
  metis_tac[endpoint_names_trans]);

val sender_is_endpoint = Q.store_thm("sender_is_endpoint",
 `∀p1 p2 q1 d q2 conf.
  trans conf p1 (LSend q1 d q2) p2 ==> MEM q1 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val receiver_is_endpoint = Q.store_thm("receiver_is_endpoint",
 `∀p1 p2 q1 d q2 conf.
  trans conf p1 (LReceive q1 d q2) p2 ==> MEM q2 (MAP FST (endpoints p1))`,
  rpt strip_tac
  >> qmatch_asmsub_abbrev_tac `trans _ _ alpha _`
  >> pop_assum (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`q1`,`d`,`q2`]
  >> pop_assum mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`alpha`,`p1`,`conf`]
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> fs[endpoints_def]);

val add_queue_def = Define `
  (add_queue p1 qe p2 payloadLang$NNil = NNil)
  ∧ (add_queue p1 qe p2 (NEndpoint p s e) =
      if p1 = p then NEndpoint p (s with queues := qpush s.queues p2 qe) e
      else NEndpoint p s e
     )
  ∧ (add_queue p1 qe p2 (NPar n1 n2) = NPar (add_queue p1 qe p2 n1) (add_queue p1 qe p2 n2))
`

Theorem trans_same_sender_determ:
  trans conf p1 (LSend q2 d1 q1) p2
  /\ trans conf p1 (LSend q2 d2 q3) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> q1 = q3 /\ d1 = d2 /\ p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`q2`,`d2`,`q1`,`d1`,`p3`,`q3`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[sender_is_endpoint]
QED

Theorem trans_same_receiver_determ:
  trans conf p1 (LReceive s d r) p2
  /\ trans conf p1 (LReceive s d r) p3
  /\ ALL_DISTINCT(MAP FST(endpoints p1))
  ==> p2 = p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`p3`,`s`,`d`,`r`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[receiver_is_endpoint]
QED

Theorem qpush_ineq[simp]:
  q ≠ qpush q p d
Proof
  rw[qpush_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
  qexists_tac ‘p’ >> rw[qlk_def,fget_def] >>
  TOP_CASE_TAC >> rw[]
QED

Theorem qpush_cong1[simp]:
  qpush q p1 d = qpush q p1' d' ⇔ p1 = p1' ∧ d = d'
Proof
  rw[qpush_def,fmap_eq_flookup,FLOOKUP_UPDATE,EQ_IMP_THM] >>
  pop_assum(qspec_then ‘p1’ mp_tac) >> rw[qlk_def,fget_def] >>
  FULL_CASE_TAC >> fs[]
QED

Theorem trans_no_selfloop:
  !conf p1 alpha p2.
  trans conf p1 alpha p2 /\ conf.payload_size > 0
  ==> p1 <> p2
Proof
  PURE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_ind >> rw[] >> fs[payloadLangTheory.state_component_equality] >>
  TRY(disj2_tac) >> spose_not_then strip_assume_tac >>
  qmatch_asmsub_abbrev_tac `a1 = a2` >>
  `endpoint_size a1 = endpoint_size a2` by simp[] >>
  pop_assum mp_tac >> unabbrev_all_tac >> rpt(pop_assum kall_tac) >>
  simp[endpoint_size_def]
QED

Theorem trans_different_sender:
  trans conf p1 (LSend s1 d1 r1) p2
  /\ trans conf p1 (LSend s2 d2 r2) p3
  /\ conf.payload_size > 0
  /\ s1 <> s2
  ==> p2 <> p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`r2`,`r1`,`d2`,`s2`,`d1`,`p3`,`s1`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> metis_tac[sender_is_endpoint,trans_no_selfloop]
QED

(* TODO: remove? strictly weaker than trans_distinct_residual *)
Theorem trans_send_receive_distinct:
  trans conf p1 (LSend s1 d1 r1) p2
  /\ trans conf p1 (LReceive s2 d2 r2) p3
  /\ conf.payload_size > 0 (* not strictly needed *)
  ==> p2 <> p3
Proof
  qmatch_goalsub_abbrev_tac `trans _ _ alpha`
  >> rpt(disch_then strip_assume_tac)
  >> pop_assum mp_tac
  >> qhdtm_x_assum `Abbrev` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> rpt(pop_assum mp_tac)
  >> MAP_EVERY qid_spec_tac [`r2`,`r1`,`d2`,`s2`,`d1`,`p3`,`s1`,`p2`,`alpha`,`p1`,`conf`]
  >> Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL]
  >> ho_match_mp_tac trans_strongind
  >> rpt conj_tac >> rpt(gen_tac ORELSE disch_then strip_assume_tac)
  >> fs[] >> rveq
  >> qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases])
  >> fs[] >> rveq >> fs[] >> rveq >> fs[endpoints_def,ALL_DISTINCT_APPEND]
  >> fs[payloadLangTheory.state_component_equality]
  >> metis_tac[sender_is_endpoint,trans_no_selfloop]
QED

Theorem trans_distinct_residual:
  !conf p1 alpha p2 beta p3.
  trans conf p1 alpha p2
  /\ trans conf p1 beta p3
  /\ alpha <> beta
  /\ conf.payload_size > 0
  ==> p2 <> p3
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL,GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac trans_strongind >> rpt strip_tac >>
  fs[] >> rveq
  >- (* Send-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Send-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Enqueue *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* Com-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      Cases_on `beta` >> fs[] >> metis_tac[trans_no_selfloop])
  >- (* Com-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >>
      Cases_on `beta` >> fs[] >> metis_tac[trans_no_selfloop])
  >- (* Dequeue-last-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* Dequeue-intermediate-payload *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality] >>
      qmatch_asmsub_abbrev_tac `a1:endpoint = a2` >>
      `endpoint_size a1 = endpoint_size a2` by simp[] >>
      unabbrev_all_tac >> pop_assum mp_tac >> rpt(pop_assum kall_tac) >>
      simp[endpoint_size_def])
  >- (* If-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* If-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Let *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[payloadLangTheory.state_component_equality])
  >- (* Par-L *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >> metis_tac[trans_no_selfloop])
  >- (* Par-R *)
     (qhdtm_x_assum `trans` (assume_tac o SIMP_RULE std_ss [Once trans_cases]) >>
      fs[] >> rveq >> fs[] >> rveq >> fs[] >> metis_tac[trans_no_selfloop])
QED

Theorem intermediate_final_IMP:
  !d. intermediate d /\ final d ==> F
Proof
  Cases >> rpt strip_tac >> fs[intermediate_def,final_def] >> rveq >> fs[]
QED

Theorem qpush_prefix:
  ∀qs spL spA dA.
    isPREFIX (qlk qs spL) (qlk (qpush qs spA dA) spL)
Proof
  rw[qlk_def,qpush_def,fget_def] >>
  Cases_on ‘spL = spA’ >>
  rw[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on ‘FLOOKUP qs spA’ >> rw[rich_listTheory.IS_PREFIX_SNOC]
QED

(* Pushing to different sender queues is commutative *)
Theorem qpush_commutes:
  ∀qs spA dA spB dB.
    spA ≠ spB ⇒
      qpush (qpush qs spA dA) spB dB =
      qpush (qpush qs spB dB) spA dA
Proof
  rw[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[finite_mapTheory.FUPDATE_COMMUTES]
QED

(* Message can't be final and intermediate *)
Theorem final_inter_mutexc:
  ∀d. ¬(intermediate d ∧ final d)
Proof
  Cases_on ‘d’ >>
  rw[intermediate_def,final_def] >>
  Cases_on ‘h ≠ 2w’ >> fs[] >>
  rw[wordsTheory.dimword_def,wordsTheory.dimindex_8]
QED

(* PAYLOAD NETWORK INVARIANTS *)
(* Contained Nodes *)
Definition net_has_node_def:
  (net_has_node NNil              _  = F)                          ∧
  (net_has_node (NPar n1 n2)      nd = (net_has_node n1 nd ∨
                                        net_has_node n2 nd   )) ∧
  (net_has_node (NEndpoint p _ _) nd = (p = nd))
End

Theorem trans_pres_nodes:
  ∀conf s0 l s1.
    trans conf s0 l s1 ⇒
      (∀nd. net_has_node s0 nd ⇔ net_has_node s1 nd)
Proof
  Induct_on ‘trans’ >> rw[net_has_node_def]
QED

(* Wellformedness *)
Definition net_wf_def:
  (net_wf NNil = T) ∧
  (net_wf (NEndpoint _ _ _) = T) ∧
  (net_wf (NPar n1 n2) ⇔ net_wf n1 ∧ net_wf n2 ∧
                         DISJOINT
                          (net_has_node n1)
                          (net_has_node n2))
End

Theorem net_has_node_MEM_endpoints:
  ∀n p. net_has_node n p ⇔ MEM p (MAP FST (endpoints n))
Proof
  Induct \\ rw [] \\ fs [endpoints_def,net_has_node_def]
  \\ metis_tac []
QED

Theorem net_wf_ALL_DISTINCT_eq:
  ∀n. ALL_DISTINCT(MAP FST(endpoints n)) ⇒ net_wf n
Proof
  Induct \\ fs [net_wf_def,endpoints_def,ALL_DISTINCT_APPEND]
  \\ fs [DISJOINT_ALT]
  \\ fs [IN_DEF,net_has_node_MEM_endpoints]
QED

Theorem trans_pres_wf:
  ∀conf s0 l s1.
    trans conf s0 l s1 ⇒
      (net_wf s0 ⇔ net_wf s1)
Proof
  Induct_on ‘trans’ >>
  rw[net_wf_def] >>
  metis_tac[trans_pres_nodes,EQ_IMP_THM]
QED

(* PAYLOAD NETWORK COMMUNICATION PROPERTIES *)
(* Necessary and Sufficient Network Receieve Conditions *)
Theorem trans_receive_cond:
  ∀conf sp N d dp.
    (sp ≠ dp ∧ net_has_node N dp) ⇔
    (∃N'. trans conf N (LReceive sp d dp) N')
Proof
  rw[EQ_IMP_THM]
  >- (Induct_on ‘N’ >> rw[net_has_node_def] >> metis_tac[trans_rules])
  >- (first_x_assum mp_tac >> Induct_on ‘trans’ >> rw[net_has_node_def])
  >- (first_x_assum mp_tac >> Induct_on ‘trans’ >> rw[net_has_node_def])
QED

(* Necessary Network Sending Conditions *)
Theorem trans_send_cond:
  ∀conf sp N d dp.
    (∃N'. trans conf N (LSend sp d dp) N') ⇒
    (sp ≠ dp ∧ net_has_node N sp)
Proof
  rw[] >> first_x_assum mp_tac >>
  Induct_on ‘trans’ >> rw[net_has_node_def]
QED

(* Well-formed Network Sending is unique *)
Theorem trans_send_unique:
  ∀conf N1 aN2 bN2 sp rp da db.
    net_wf N1 ∧
    trans conf N1 (LSend sp da rp) aN2 ∧
    trans conf N1 (LSend sp db rp) bN2 ⇒
    da = db
Proof
  Induct_on ‘N1’
  >- (rw[] >>
      ‘net_has_node NNil sp’
        by metis_tac[trans_send_cond] >>
      fs[net_has_node_def])
  >- (rw[] >>
      fs[net_wf_def] >>
      rpt (qpat_x_assum ‘trans _ (NPar _ _) _ _’
           (assume_tac o ONCE_REWRITE_RULE [trans_cases])) >>
      fs[]
      >- rpt (first_x_assum (dxrule_then strip_assume_tac))
      >- (rename1 ‘DISJOINT (net_has_node N1A) (net_has_node N1B)’ >>
          ‘sp ∈ net_has_node N1A ∧ sp ∈ net_has_node N1B’
            suffices_by (rw[] >>
                        fs[IN_DISJOINT] >>
                        first_x_assum (qspec_then ‘sp’ assume_tac) >>
                        rfs[]) >>
          metis_tac[trans_send_cond,IN_APP])
      >- (rename1 ‘DISJOINT (net_has_node N1A) (net_has_node N1B)’ >>
          ‘sp ∈ net_has_node N1A ∧ sp ∈ net_has_node N1B’
            suffices_by (rw[] >>
                        fs[IN_DISJOINT] >>
                        first_x_assum (qspec_then ‘sp’ assume_tac) >>
                        rfs[]) >>
          metis_tac[trans_send_cond,IN_APP])
      >- rpt (first_x_assum (dxrule_then strip_assume_tac)))
  >- (rw[] >>
      ntac 2 (fs[Once trans_cases]) >>
      rfs[])
QED

(* CONFLUENCE *)
(* Restrictions of wf labels for confluence *)
Definition wf_label_def:
  wf_label N L =
    case L of
      LSend    sp d rp => ¬(net_has_node N rp)
    | LReceive sp d rp => ¬(net_has_node N sp)
    | LTau             => T
End

(* Restrictions of compatible labels for confluence *)
Definition compat_labels_def:
  compat_labels LA LB =
    ∀sp1 d1 rp1 sp2 d2 rp2.
      (LA = LReceive sp1 d1 rp1) ∧
      (LB = LReceive sp2 d2 rp2) ⇒
      (sp1 ≠ sp2 ∨ d1 = d2 ∨ rp1 ≠ rp2)
End

(* Basic theorem about generating compatible receive labels *)
Theorem send_gen_compat:
  ∀N1 N2A N2B spA dA rpA spB dB rpB.
    net_wf N1 ∧
    trans conf N1 (LSend spA dA rpA) N2A ∧
    trans conf N1 (LSend spB dB rpB) N2B ⇒
    compat_labels (LReceive spA dA rpA) (LReceive spB dB rpB)
Proof
  simp[compat_labels_def] >>
  Induct_on ‘N1’
  >- rw[Once trans_cases]
  >- (rw[] >>
      rename [‘net_wf (NPar N1a N1b)’] >>
      ‘net_wf N1a ∧ net_wf N1b’
        by fs[net_wf_def] >>
      fs[] >>
      rpt (qpat_x_assum ‘trans conf (NPar _ _) _ _’
                        (assume_tac o ONCE_REWRITE_RULE [trans_cases])) >>
      fs[] >> TRY (metis_tac []) >> CCONTR_TAC >>
      ‘net_has_node N1a spA ∧ net_has_node N1b spA’
        suffices_by metis_tac[net_wf_def,
                              DISJOINT_SYM,
                              DISJOINT_ALT,
                              IN_APP] >>
      metis_tac[trans_send_cond])
  >- (rw[Once trans_cases] >>
      fs[Once trans_cases] >>
      fs[])
QED

(*  Confluence Result for different Labels *)
Theorem trans_diff_diamond:
  ∀N1 LA N2A LB N2B.
    net_wf N1 ∧
    wf_label N1 LA ∧
    wf_label N1 LB ∧
    LA ≠ LB ∧
    compat_labels LA LB ∧
    trans conf N1 LA N2A ∧
    trans conf N1 LB N2B ⇒
    ∃N3.
      trans conf N2A LB N3 ∧
      trans conf N2B LA N3
Proof
  Induct_on ‘trans’ >>
  rw[] >> pop_assum (fn x => strip_assume_tac(REWRITE_RULE [Once trans_cases] x)) >>
  fs[] >> rw[] >> fs[compat_labels_def]
  (* LSend Final/LRecieve *)
  >- (rename [‘NEndpoint c s e’,‘NEndpoint _ (_ with queues := _) _’,‘LReceive sp rd c’] >>
      qmatch_goalsub_abbrev_tac ‘s with queues := nqs’ >>
      qexists_tac ‘NEndpoint c (s with queues := nqs) e’ >>
      rw[]
      >- metis_tac[trans_rules]
      >- (irule (hd (CONJUNCTS trans_rules)) >>
          simp[]))
  (* LSend Intermediate/LRecieve *)
  >- (rename [‘Send rp sv n e’,‘Send rp sv (n + _) e’,
             ‘LReceive sp rd c’] >>
      qmatch_goalsub_abbrev_tac ‘s with queues := nqs’ >>
      qexists_tac ‘NEndpoint c (s with queues := nqs) (Send rp sv (n + conf.payload_size) e)’ >>
      rw[]
      >- metis_tac[trans_rules]
      >- (irule (el 2 (CONJUNCTS trans_rules)) >>
         simp[]))
  (* LRecieve/LSend Final *)
  >- (rename [‘NEndpoint c s e’,‘NEndpoint _ (_ with queues := _) _’,‘LReceive sp rd c’] >>
      qmatch_goalsub_abbrev_tac ‘s with queues := nqs’ >>
      qexists_tac ‘NEndpoint c (s with queues := nqs) e’ >>
      rw[]
      >- (irule (hd (CONJUNCTS trans_rules)) >>
          simp[])
      >- metis_tac[trans_rules])
  (* LRecieve/LSend Intermediate *)
  >- (rename [‘Send rp sv n e’,‘Send rp sv (n + _) e’,
             ‘LReceive sp rd c’] >>
      qmatch_goalsub_abbrev_tac ‘s with queues := nqs’ >>
      qexists_tac ‘NEndpoint c (s with queues := nqs) (Send rp sv (n + conf.payload_size) e)’ >>
      rw[]
      >- (irule (el 2 (CONJUNCTS trans_rules)) >>
         simp[])
      >- metis_tac[trans_rules])
  (* LReceive/LReceive *)
  >- (rename [‘LReceive sp1 d1 c’,‘sp1 = sp2 ⇒ d2 = d1’] >>
      Cases_on ‘sp1 = sp2’
      >- fs[]
      >- (qexists_tac ‘NEndpoint c (s with queues := qpush (qpush s.queues sp1 d1) sp2 d2) e’ >>
          rw[]
          >- (qspecl_then [‘s.queues’,‘sp1’,‘d1’,‘sp2’,‘d2’] assume_tac
                          qpush_commutes >>
              rfs[] >> first_x_assum SUBST1_TAC >>
              qmatch_goalsub_abbrev_tac ‘trans conf (NEndpoint c os e) _ _’ >>
              ‘qpush s.queues sp2 d2 = os.queues’
                by rw[Abbr ‘os’] >>
              first_x_assum SUBST1_TAC >>
              qmatch_goalsub_abbrev_tac ‘trans _ _ _ (NEndpoint _ ns _)’ >>
              ‘ns = os with queues := qpush os.queues sp1 d1’
                by rw[Abbr ‘ns’,Abbr ‘os’] >>
              metis_tac[trans_rules])
          >- (qmatch_goalsub_abbrev_tac ‘trans conf (NEndpoint c os e) _ _’ >>
              ‘qpush s.queues sp1 d1 = os.queues’
                by rw[Abbr ‘os’] >>
              first_x_assum SUBST1_TAC >>
              qmatch_goalsub_abbrev_tac ‘trans _ _ _ (NEndpoint _ ns _)’ >>
              ‘ns = os with queues := qpush os.queues sp2 d2’
                by rw[Abbr ‘ns’,Abbr ‘os’] >>
              metis_tac[trans_rules])))
  (* LReceive/LReceive *)
  >- (rename [‘LReceive sp1 d1 c’,‘sp1 = sp2 ⇒ d2 = d1’] >>
      Cases_on ‘sp1 = sp2’
      >- fs[]
      >- (qexists_tac ‘NEndpoint c (s with queues := qpush (qpush s.queues sp1 d1) sp2 d2) e’ >>
          rw[]
          >- (qspecl_then [‘s.queues’,‘sp1’,‘d1’,‘sp2’,‘d2’] assume_tac
                          qpush_commutes >>
              rfs[] >> first_x_assum SUBST1_TAC >>
              qmatch_goalsub_abbrev_tac ‘trans conf (NEndpoint c os e) _ _’ >>
              ‘qpush s.queues sp2 d2 = os.queues’
                by rw[Abbr ‘os’] >>
              first_x_assum SUBST1_TAC >>
              qmatch_goalsub_abbrev_tac ‘trans _ _ _ (NEndpoint _ ns _)’ >>
              ‘ns = os with queues := qpush os.queues sp1 d1’
                by rw[Abbr ‘ns’,Abbr ‘os’] >>
              metis_tac[trans_rules])
          >- (qmatch_goalsub_abbrev_tac ‘trans conf (NEndpoint c os e) _ _’ >>
              ‘qpush s.queues sp1 d1 = os.queues’
                by rw[Abbr ‘os’] >>
              first_x_assum SUBST1_TAC >>
              qmatch_goalsub_abbrev_tac ‘trans _ _ _ (NEndpoint _ ns _)’ >>
              ‘ns = os with queues := qpush os.queues sp2 d2’
                by rw[Abbr ‘ns’,Abbr ‘os’] >>
              metis_tac[trans_rules])))
  (* LReceive/LTau (Receive Final) *)
  >- (rename [‘NEndpoint c (s with queues := _) (Receive sp2 sv2 ds2 e)’,
              ‘LReceive sp d c’] >>
      qmatch_goalsub_abbrev_tac ‘<|bindings := fb; queues := bfq |>’ >>
      qexists_tac ‘NEndpoint c <|bindings := fb; queues := qpush bfq sp d|> e’ >>
      rw[]
      >- (qunabbrev_tac ‘bfq’ >> qunabbrev_tac ‘fb’ >>
          qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint _ sq (Receive _ _ _ _)) _
                                             (NEndpoint _ ns _)’ >>
          rename1 ‘qlk s.queues sp2 = dr::tl’ >>
          ‘∃tln. qlk sq.queues sp2 = dr::tln’
            by (qunabbrev_tac ‘sq’ >>
                fs[qlk_def,fget_def,qpush_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> Cases_on ‘FLOOKUP s.queues sp2’ >>
                fs[] >> metis_tac[]) >>
          ‘ns = sq with
                <|queues := normalise_queues(sq.queues |+ (sp2,tln));
                  bindings := sq.bindings |+ (sv2,FLAT (SNOC (unpad dr) ds2)) |>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[normalise_queues_qpush,DRESTRICT_normalise_queues,
                   FLOOKUP_normalise_queues_FUPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[] >-
                  (fs[APPEND_EQ_CONS] >> rveq >> fs[] >>
                   fs[qpush_def,SNOC_APPEND,FUPDATE_EQ] >>
                   rw[normalise_queues_FUPDATE_FUPDATE] >>
                   rw[normalise_queues_FUPDATE_NONEMPTY]) >>
                fs[qpush_def] >> rveq >> fs[FUPDATE_COMMUTES] >>
                simp[SimpR“$=”,Once normalise_queues_FUPDATE_NONEMPTY]) >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules])
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint c s0 e) _ (NEndpoint c s1 e)’ >>
          ‘s1 = s0 with queues := qpush s0.queues sp d’
            by (qunabbrev_tac ‘s0’ >> qunabbrev_tac ‘s1’ >> rw[]) >>
          rw[] >> metis_tac[trans_rules]))
  (* LReceive/LTau (Receive intermediate)  *)
  >- (rename [‘NEndpoint c (s with queues := _) (Receive sp2 sv2 ds2 e)’,
              ‘LReceive sp d c’,‘qlk s.queues sp2 = dr::tl’] >>
      qexists_tac ‘NEndpoint c (s with queues := normalise_queues(qpush (s.queues |+ (sp2,tl)) sp d))
                               (Receive sp2 sv2 (SNOC (unpad dr) ds2) e)’ >>
      rw[]
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint _ sq (Receive _ _ _ _)) _
                                             (NEndpoint _ ns _)’ >>
          ‘∃tln. qlk sq.queues sp2 = dr::tln’
            by (qunabbrev_tac ‘sq’ >>
                fs[qlk_def,fget_def,qpush_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> Cases_on ‘FLOOKUP s.queues sp2’ >>
                fs[] >> metis_tac[]) >>
          ‘ns = sq with
                <|queues := normalise_queues(sq.queues |+ (sp2,tln))|>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[]
                >- (rfs[] >> rw[listTheory.SNOC_APPEND] >> rw[normalise_queues_FUPDATE_NONEMPTY])
                >- (rw[finite_mapTheory.FUPDATE_COMMUTES,normalise_queues_FUPDATE_NONEMPTY])) >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules])
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint _ s0 _) _ (NEndpoint _ s1 _)’ >>
          ‘s1 = s0 with queues := qpush s0.queues sp d’
            by (qunabbrev_tac ‘s0’ >> qunabbrev_tac ‘s1’ >> rw[]) >>
          rw[] >> metis_tac[trans_rules]))
  (* LReceive/LTau (IfThen true) *)
  >- (rename [‘NEndpoint c (s with queues := qpush s.queues sp d) (IfThen cv e _)’] >>
      qexists_tac ‘NEndpoint c (s with queues := qpush s.queues sp d) e’ >>
      rw[]
      >- (qmatch_goalsub_abbrev_tac ‘NEndpoint c sq’ >>
          ‘s.bindings = sq.bindings’
            by simp[Abbr ‘sq’] >>
          rw[] >>
          metis_tac[trans_rules])
      >- metis_tac[trans_rules])
  (* LReceive/LTau (IfThen false) *)
  >- (rename [‘NEndpoint c (s with queues := qpush s.queues sp d) (IfThen cv _ e)’] >>
      qexists_tac ‘NEndpoint c (s with queues := qpush s.queues sp d) e’ >>
      rw[]
      >- (qmatch_goalsub_abbrev_tac ‘NEndpoint c sq’ >>
          ‘s.bindings = sq.bindings’
            by simp[Abbr ‘sq’] >>
          rw[] >>
          metis_tac[trans_rules])
      >- metis_tac[trans_rules])
  (* LReceive/LTau (Let statement) *)
  >- (rename [‘NEndpoint c (s with queues := _) (Let _ _ _ e)’] >>
      qmatch_goalsub_abbrev_tac ‘s with queues := nq’ >>
      qmatch_goalsub_abbrev_tac ‘s with bindings := nb’ >>
      qexists_tac ‘NEndpoint c (s with <|bindings := nb; queues := nq|>) e’ >>
      rw[]
      >- (qabbrev_tac ‘IS = s with queues := nq’ >>
          ‘<|bindings := nb; queues := nq|> = IS with bindings := nb’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          qunabbrev_tac ‘nb’ >>
          ‘s.bindings = IS.bindings’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          irule (el 10 (CONJUNCTS trans_rules)) >>
          simp[Abbr ‘IS’])
      >- (qabbrev_tac ‘IS = s with bindings := nb’ >>
          ‘<|bindings := nb; queues := nq|> = IS with queues := nq’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          qunabbrev_tac ‘nq’ >>
          ‘s.queues = IS.queues’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules]))
  (* LTau (Internal Comms TO RIGHT) / Parallel Embedded Behaviour (ON LEFT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N2Aa N2Ab) _ _ ∧
               trans conf (NPar N2Ba N1b) _ _’] >>
      last_x_assum (qspecl_then [‘LB’,‘N2Ba’] assume_tac) >>
      ‘net_wf N1a’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘LSend p1 d p2 ≠ LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’,
                    ‘trans conf N1a (LSend p1 d p2) N2Aa’,
                    ‘trans conf N1b (LReceive p1 d p2) N2Ab’] >>
            ‘p2 ≠ nint’
              suffices_by rw[] >>
            CCONTR_TAC >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1b nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_receive_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a (LSend p1 d p2)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1b p2’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_receive_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Aa LB N3’,
              ‘trans conf N2Ba (LSend p1 d p2) N3’] >>
      qexists_tac ‘NPar N3 N2Ab’ >>
      metis_tac[trans_rules])
  (* LTau (Internal Comms TO RIGHT) / Parallel Embedded Behaviour (ON RIGHT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N2Aa N2Ab) _ _ ∧
               trans conf (NPar N1a N2Bb) _ _’] >>
      first_x_assum (qspecl_then [‘LB’,‘N2Bb’] assume_tac) >>
      ‘net_wf N1b’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘∀ds. LReceive p1 ds p2 ≠ LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’,
                    ‘trans conf N1a (LSend p1 d p2) N2Aa’,
                    ‘trans conf N1b (LReceive p1 d p2) N2Ab’] >>
            ‘p1 ≠ nint’
              suffices_by rw[] >>
            CCONTR_TAC >>
            fs[] >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1a nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_send_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b (LReceive p1 d p2)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1a p1’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_send_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Ab LB N3’,
              ‘trans conf N2Bb (LReceive p1 d p2) N3’] >>
      qexists_tac ‘NPar N2Aa N3’ >>
      metis_tac[trans_rules])
  (* LTau (Internal Comms TO LEFT) / Parallel Embedded Behaviour (ON LEFT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N2Aa N2Ab) _ _ ∧
               trans conf (NPar N2Ba N1b) _ _’] >>
      last_x_assum (qspecl_then [‘LB’,‘N2Ba’] assume_tac) >>
      ‘net_wf N1a’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘∀ds. LReceive p1 ds p2 ≠ LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’,
                    ‘trans conf N1a (LReceive p1 d p2) N2Aa’,
                    ‘trans conf N1b (LSend p1 d p2) N2Ab’] >>
            ‘p1 ≠ nint’
              suffices_by rw[] >>
            CCONTR_TAC >>
            fs[] >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1b nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_send_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a (LReceive p1 d p2)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1b p1’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_send_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Aa LB N3’,
              ‘trans conf N2Ba (LReceive p1 d p2) N3’] >>
      qexists_tac ‘NPar N3 N2Ab’ >>
      metis_tac[trans_rules])
  (* LTau (Internal Comms TO LEFT) / Other Behaviour (ON RIGHT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N2Aa N2Ab) _ _ ∧
               trans conf (NPar N1a N2Bb) _ _’] >>
      first_x_assum (qspecl_then [‘LB’,‘N2Bb’] assume_tac) >>
      ‘net_wf N1b’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘LSend p1 d p2 ≠ LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’,
                    ‘trans conf N1a (LReceive p1 d p2) N2Aa’,
                    ‘trans conf N1b (LSend p1 d p2) N2Ab’] >>
            ‘p2 ≠ nint’
              suffices_by rw[] >>
            CCONTR_TAC >>
            fs[] >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1a nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_receive_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b LB’
        by (Cases_on ‘LB’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b (LSend p1 d p2)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1a p2’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_receive_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Ab LB N3’,
              ‘trans conf N2Bb (LSend p1 d p2) N3’] >>
      qexists_tac ‘NPar N2Aa N3’ >>
      metis_tac[trans_rules])
  (* LReceive/LTau (Receive Final) *)
  >- (rename [‘NEndpoint c (s with queues := _) (Receive sp2 sv2 ds2 e)’,
              ‘LReceive sp d c’] >>
      qmatch_goalsub_abbrev_tac ‘<|bindings := fb; queues := bfq |>’ >>
      qexists_tac ‘NEndpoint c <|bindings := fb; queues := normalise_queues(qpush bfq sp d)|> e’ >>
      rw[]
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint c s0 e) _ (NEndpoint c s1 e)’ >>
          ‘s1 = s0 with queues := qpush s0.queues sp d’
            by (qunabbrev_tac ‘s0’ >> qunabbrev_tac ‘s1’ >> rw[Abbr ‘bfq’]) >>
          rw[] >> metis_tac[trans_rules])
      >- (qunabbrev_tac ‘bfq’ >> qunabbrev_tac ‘fb’ >>
          qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint _ sq (Receive _ _ _ _)) _
                                             (NEndpoint _ ns _)’ >>
          rename1 ‘qlk s.queues sp2 = dr::tl’ >>
          ‘∃tln. qlk sq.queues sp2 = dr::tln’
            by (qunabbrev_tac ‘sq’ >>
                fs[qlk_def,fget_def,qpush_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> Cases_on ‘FLOOKUP s.queues sp2’ >>
                fs[] >> metis_tac[]) >>
          ‘ns = sq with
                <|queues := normalise_queues(sq.queues |+ (sp2,tln));
                  bindings := sq.bindings |+ (sv2,FLAT (SNOC (unpad dr) ds2)) |>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[]
                >- (rfs[] >> rw[listTheory.SNOC_APPEND] >> rw[normalise_queues_FUPDATE_NONEMPTY])
                >- (rw[finite_mapTheory.FUPDATE_COMMUTES,normalise_queues_FUPDATE_NONEMPTY])) >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules]))
  (* LTau (Receive intermediate)/LReceive  *)
  >- (rename [‘NEndpoint c (s with queues := _) (Receive sp2 sv2 (SNOC (unpad dr) ds2) e)’,
              ‘LReceive sp d c’,‘qlk s.queues sp2 = dr::tl’] >>
      qexists_tac ‘NEndpoint c (s with queues := normalise_queues(qpush (s.queues |+ (sp2,tl)) sp d))
                               (Receive sp2 sv2 (SNOC (unpad dr) ds2) e)’ >>
      rw[]
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint _ s0 _) _ (NEndpoint _ s1 _)’ >>
          ‘s1 = s0 with queues := qpush s0.queues sp d’
            by (qunabbrev_tac ‘s0’ >> qunabbrev_tac ‘s1’ >> rw[]) >>
          rw[] >> metis_tac[trans_rules])
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint _ sq (Receive _ _ _ _)) _
                                             (NEndpoint _ ns _)’ >>
          ‘∃tln. qlk sq.queues sp2 = dr::tln’
            by (qunabbrev_tac ‘sq’ >>
                fs[qlk_def,fget_def,qpush_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> Cases_on ‘FLOOKUP s.queues sp2’ >>
                fs[] >> metis_tac[]) >>
          ‘ns = sq with
                <|queues := normalise_queues(sq.queues |+ (sp2,tln))|>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[]
                >- (rfs[] >> rw[listTheory.SNOC_APPEND] >> rw[normalise_queues_FUPDATE_NONEMPTY])
                >- (rw[finite_mapTheory.FUPDATE_COMMUTES,normalise_queues_FUPDATE_NONEMPTY])) >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules]))
  (* LTau (IfThen true)/LReceive *)
  >- (rename [‘NEndpoint c (s with queues := qpush s.queues sp d) (IfThen cv e _)’] >>
      qexists_tac ‘NEndpoint c (s with queues := qpush s.queues sp d) e’ >>
      rw[]
      >- metis_tac[trans_rules]
      >- (qmatch_goalsub_abbrev_tac ‘NEndpoint c sq’ >>
          ‘s.bindings = sq.bindings’
            by simp[Abbr ‘sq’] >>
          rw[] >>
          metis_tac[trans_rules]))
  (* LTau (IfThen false)/LReceive *)
  >- (rename [‘NEndpoint c (s with queues := qpush s.queues sp d) (IfThen cv _ e)’] >>
      qexists_tac ‘NEndpoint c (s with queues := qpush s.queues sp d) e’ >>
      rw[]
      >- metis_tac[trans_rules]
      >- (qmatch_goalsub_abbrev_tac ‘NEndpoint c sq’ >>
          ‘s.bindings = sq.bindings’
            by simp[Abbr ‘sq’] >>
          rw[] >>
          metis_tac[trans_rules]))
  (* LTau (Let statement)/LReceive *)
  >- (rename [‘NEndpoint c (s with queues := _) (Let _ _ _ e)’] >>
      qmatch_goalsub_abbrev_tac ‘s with queues := nq’ >>
      qmatch_goalsub_abbrev_tac ‘s with bindings := nb’ >>
      qexists_tac ‘NEndpoint c (s with <|bindings := nb; queues := nq|>) e’ >>
      rw[]
      >- (qabbrev_tac ‘IS = s with bindings := nb’ >>
          ‘<|bindings := nb; queues := nq|> = IS with queues := nq’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          qunabbrev_tac ‘nq’ >>
          ‘s.queues = IS.queues’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules])
      >- (qabbrev_tac ‘IS = s with queues := nq’ >>
          ‘<|bindings := nb; queues := nq|> = IS with bindings := nb’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          qunabbrev_tac ‘nb’ >>
          ‘s.bindings = IS.bindings’
            by simp[Abbr ‘IS’] >>
          first_x_assum SUBST1_TAC >>
          irule (el 10 (CONJUNCTS trans_rules)) >>
          simp[Abbr ‘IS’]))
  (* Parallel Embedded Behaviour (ON LEFT)/LTau (Internal Comms TO RIGHT) /  *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N2Aa N1b)  _ _ ∧
               trans conf (NPar N2Ba N2Bb) _ _’] >>
      last_x_assum (qspecl_then [‘LSend p1 d p2’,‘N2Ba’] assume_tac) >>
      ‘net_wf N1a’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘LA ≠ LSend p1 d p2’
        by (Cases_on ‘LA’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’,
                    ‘trans conf N1a (LSend p1 d p2) N2Aa’,
                    ‘trans conf N1b (LReceive p1 d p2) N2Ab’] >>
            ‘p2 ≠ nint’
              suffices_by rw[] >>
            CCONTR_TAC >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1b nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_receive_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a LA’
        by (Cases_on ‘LA’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a (LSend p1 d p2)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1b p2’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_receive_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Aa (LSend p1 d p2) N3’,
              ‘trans conf N2Ba LA N3’] >>
      qexists_tac ‘NPar N3 N2Bb’ >>
      metis_tac[trans_rules])
  (*  Parallel Embedded Behaviour (ON LEFT) / LTau (Internal Comms TO RIGHT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘LReceive sp d rp’,
              ‘trans conf (NPar N2Aa N1b) _ _ ∧
               trans conf (NPar N2Ba N2Bb) _ _’] >>
      first_x_assum (qspecl_then [‘LReceive sp d rp’,‘N2Ba’] assume_tac) >>
      ‘net_wf N1a’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘∀ds. LReceive sp ds rp ≠ LA’
        by (Cases_on ‘LA’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’,
                    ‘trans conf N1a (LReceive sp d rp) N2Aa’,
                    ‘trans conf N1b (LSend sp d rp) N2Ab’] >>
            DISJ1_TAC >> CCONTR_TAC >> fs[] >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1b nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_send_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a LA’
        by (Cases_on ‘LA’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1a (LReceive sp d rp)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1b sp’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_send_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Ba LA N3’,
              ‘trans conf N2Aa (LReceive sp d rp) N3’] >>
      qexists_tac ‘NPar N3 N2Bb’ >>
      metis_tac[trans_rules])
  (* Parallel Embeded Behaviour (ON LEFT) / Parallel Embedded Behaviour (ON LEFT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N2Aa N1b) _ _ ∧
               trans conf (NPar N2Ba N1b) _ _’] >>
      last_x_assum (qspecl_then [‘LB’,‘N2Ba’] assume_tac) >>
      ‘net_wf N1a’
        by fs[net_wf_def] >>
      ‘wf_label N1a LA’
        by (Cases_on ‘LA’ >>
            fs[wf_label_def,net_has_node_def]) >>
      ‘wf_label N1a LB’
        by (Cases_on ‘LB’ >>
            fs[wf_label_def,net_has_node_def]) >>
      fs[] >> ntac 3 (pop_assum (K ALL_TAC)) >>
      qmatch_asmsub_abbrev_tac ‘predA ∧ predB ∧ predC ⇒
                                ∃N3. trans conf N2Aa LB N3 ∧
                                     trans conf N2Ba LA N3’ >>
      qpat_x_assum ‘predA’ assume_tac >>
      qpat_x_assum ‘predB’ assume_tac >>
      qpat_x_assum ‘predC’ assume_tac >>
      fs[] >> ntac 6 (pop_assum (K ALL_TAC)) >>
      qexists_tac ‘NPar N3 N1b’ >>
      metis_tac[trans_rules])
  (* Parallel Embeded Behaviour (ON LEFT) / Parallel Embedded Behaviour (ON RIGHT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N2Aa N1b) _ _ ∧
               trans conf (NPar N1a N2Bb) _ _’] >>
      qexists_tac ‘NPar N2Aa N2Bb’ >>
      metis_tac[trans_rules])
  (* Parallel Embedded Behaviour (ON RIGHT) / LTau (Internal Comms TO RIGHT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘LReceive sp d rp’,
              ‘trans conf (NPar N1a N2Ab) _ _ ∧
               trans conf (NPar N2Ba N2Bb) _ _’] >>
      last_x_assum (qspecl_then [‘LReceive sp d rp’,‘N2Bb’] assume_tac) >>
      ‘net_wf N1b’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘∀ds. LReceive sp ds rp ≠ LA’
        by (Cases_on ‘LA’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’] >>
            DISJ1_TAC >>
            CCONTR_TAC >>
            fs[] >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1a nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_send_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b LA’
        by (Cases_on ‘LA’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b (LReceive sp d rp)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1a sp’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_send_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Ab (LReceive sp d rp) N3’,
              ‘trans conf N2Bb  LA N3’] >>
      qexists_tac ‘NPar N2Ba N3’ >>
      metis_tac[trans_rules])
  (* Parallel Embedded Behaviour (ON RIGHT) / LTau (Internal Comms TO LEFT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
          ‘LReceive sp d rp’,
              ‘trans conf (NPar N1a N2Ab) _ _ ∧
               trans conf (NPar N2Ba N2Bb) _ _’] >>
      first_x_assum (qspecl_then [‘LSend sp d rp’,‘N2Bb’] assume_tac) >>
      ‘net_wf N1b’
        by fs[net_wf_def] >>
      fs[] >> rfs[] >>
      first_x_assum (K ALL_TAC) >>
      ‘LA ≠ LSend sp d rp’
        by (Cases_on ‘LA’ >> fs[wf_label_def] >>
            rename [‘¬net_has_node (NPar N1a N1b) nint’] >>
            ‘rp ≠ nint’
              suffices_by rw[] >>
            CCONTR_TAC >>
            ‘net_has_node (NPar N1a N1b) nint’
              by (‘net_has_node N1a nint’
                    suffices_by fs[net_has_node_def] >>
                  metis_tac[trans_receive_cond])) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b LA’
        by (Cases_on ‘LA’ >> fs[wf_label_def,net_has_node_def]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      ‘wf_label N1b (LSend sp d rp)’
        by (rw[wf_label_def] >>
            ‘net_has_node N1a rp’
              suffices_by (metis_tac[net_wf_def,
                                     DISJOINT_SYM,
                                     DISJOINT_ALT,
                                     IN_APP]) >>
            metis_tac[trans_receive_cond]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      rename [‘trans conf N2Ab (LSend sp d rp) N3’,
              ‘trans conf N2Bb LA N3’] >>
      qexists_tac ‘NPar N2Ba N3’ >>
      metis_tac[trans_rules])
  (* Parallel Embedded Behaviour (ON RIGHT) / Parallel Embedded Behaviour (ON LEFT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N1a N2Ab) _ _ ∧
               trans conf (NPar N2Ba N1b) _ _’] >>
      qexists_tac ‘NPar N2Ba N2Ab’ >>
      metis_tac[trans_rules])
  (* Parallel Embedded Behaviour (ON RIGHT) / Parallel Embedded Behaviour (ON RIGHT) *)
  >- (rename [‘net_wf (NPar N1a N1b)’,
              ‘trans conf (NPar N1a N2Ab) _ _ ∧
               trans conf (NPar N1a N2Bb) _ _’] >>
      last_x_assum (qspecl_then [‘LB’,‘N2Bb’] assume_tac) >>
      ‘net_wf N1b’
        by fs[net_wf_def] >>
      ‘wf_label N1b LA’
        by (Cases_on ‘LA’ >>
            fs[wf_label_def,net_has_node_def]) >>
      ‘wf_label N1b LB’
        by (Cases_on ‘LB’ >>
            fs[wf_label_def,net_has_node_def]) >>
      fs[] >> ntac 3 (pop_assum (K ALL_TAC)) >>
      qmatch_asmsub_abbrev_tac ‘predA ∧ predB ∧ predC ⇒
                                ∃N3. trans conf N2Ab LB N3 ∧
                                     trans conf N2Bb LA N3’ >>
      qpat_x_assum ‘predA’ assume_tac >>
      qpat_x_assum ‘predB’ assume_tac >>
      qpat_x_assum ‘predC’ assume_tac >>
      fs[] >> ntac 6 (pop_assum (K ALL_TAC)) >>
      qexists_tac ‘NPar N1a N3’ >>
      metis_tac[trans_rules])
QED

(* Confluence Results for identical Labels *)
(* -- Functional nature for non-tau labels *)
Theorem trans_notau_functional:
  ∀conf N1 N2A N2B L.
    L ≠ LTau ∧
    trans conf N1 L N2A ∧
    trans conf N1 L N2B ∧
    net_wf N1 ⇒
    N2A = N2B
Proof
  Cases_on ‘L’ >> fs[] >>
  Induct_on ‘trans’ >> rw[]
  >- (fs[Once trans_cases] >>
      rename1 ‘LENGTH d2 > n + conf.payload_size’ >>
      ‘LENGTH d2 ≤ n + conf.payload_size’
        by fs[pad_def] >>
      fs[])
  >- (fs[Once trans_cases] >>
      rename1 ‘LENGTH d2 ≤ n + conf.payload_size’ >>
      ‘LENGTH d2 > n + conf.payload_size’
        by fs[pad_def] >>
      fs[])
  >- (fs[net_wf_def,DISJOINT_DEF,
         EXTENSION,IN_DEF] >>
      rename [‘LSend sp d rp’,‘NPar N1A N1B’] >>
      ‘¬(∃N1BS. trans conf N1B (LSend sp d rp) N1BS)’
        by metis_tac[trans_send_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
  >- (fs[net_wf_def,DISJOINT_DEF,
         EXTENSION,IN_DEF] >>
      rename [‘LSend sp d rp’,‘NPar N1A N1B’] >>
      ‘¬(∃N1AS. trans conf N1A (LSend sp d rp) N1AS)’
        by metis_tac[trans_send_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
  >- fs[Once trans_cases]
  >- (fs[net_wf_def,DISJOINT_DEF,
         EXTENSION,IN_DEF] >>
      rename [‘LReceive sp d rp’,‘NPar N1A N1B’] >>
      ‘¬(∃N1BR. trans conf N1B (LReceive sp d rp) N1BR)’
        by metis_tac[trans_receive_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
  >- (fs[net_wf_def,DISJOINT_DEF,
         EXTENSION,IN_DEF] >>
      rename [‘LReceive sp d rp’,‘NPar N1A N1B’] >>
      ‘¬(∃N1AR. trans conf N1A (LReceive sp d rp) N1AR)’
        by metis_tac[trans_receive_cond] >>
      fs[] >>
      ntac 2 (last_x_assum assume_tac) >>
      first_x_assum (assume_tac o REWRITE_RULE [Once trans_cases]) >>
      rfs[])
QED

(* -- Confluence: Identical tau labels *)
Theorem trans_samelab_tau_difout_diamond[local]:
  ∀N1 N2A N2B.
    net_wf N1 ∧
    N2A ≠ N2B ∧
    trans conf N1 LTau N2A ∧
    trans conf N1 LTau N2B ⇒
    ∃N3.
      trans conf N2A LTau N3 ∧
      trans conf N2B LTau N3
Proof
        Induct_on ‘N1’
  (* NNil Case *)
  >- (rw[] >> fs[Once trans_cases])
  (* NPar Case *)
  >- (rw[] >> rename1 ‘net_wf (NPar N1a N1b)’ >>
      qpat_x_assum ‘trans _ (NPar _ _) _ N2A’
                  (fn x => strip_assume_tac(REWRITE_RULE [Once trans_cases] x)) >>
      fs[] >> rw[] >> fs[] >>
      qpat_x_assum ‘trans _ (NPar _ _) _ _’
                  (fn x => strip_assume_tac(REWRITE_RULE [Once trans_cases] x)) >>
      fs[] >> rw[] >> fs[]
      (* (FIRST DIFF) Internal Comms (TO RIGHT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                     trans conf (NPar N2Ba N2Bb) LTau _’,
                    ‘net_wf (NPar N1a N1b)’,
                    ‘trans conf N1a (LSend spA dA rpA) N2Aa’,
                    ‘trans conf N1a (LSend spB dB rpB) N2Ba’] >>
          ‘∃N3a.
            trans conf N2Aa (LSend spB dB rpB) N3a ∧
            trans conf N2Ba (LSend spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def]
                >- (CCONTR_TAC >>
                    ‘N2Aa = N2Ba’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LSend spB dB rpB’,
                                            ‘N1a’,‘conf’] >>
                    fs[net_wf_def])
                >- (qexists_tac ‘N1a’ >>
                    fs[net_wf_def,wf_label_def,compat_labels_def] >>
                    ‘net_has_node N1b rpA ∧ net_has_node N1b rpB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_receive_cond])) >>
          ‘∃N3b.
            trans conf N2Ab (LReceive spB dB rpB) N3b ∧
            trans conf N2Bb (LReceive spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[]
                >- (CCONTR_TAC >>
                    ‘N2Aa = N2Ba’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LSend spB dB rpB’,
                                            ‘N1a’,‘conf’] >>
                    fs[net_wf_def])
                >- metis_tac[send_gen_compat,net_wf_def]
                >- (qexists_tac ‘N1b’ >>
                    fs[net_wf_def,wf_label_def,compat_labels_def] >>
                    ‘net_has_node N1a spA ∧ net_has_node N1a spB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_send_cond])) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO RIGHT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend spA dA rpA) N2Aa’,
                  ‘trans conf N1a (LSend spB dB rpB) N2Ba’] >>
          ‘∃N3a.
            trans conf N2Aa (LSend spB dB rpB) N3a ∧
            trans conf N2Ba (LSend spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def]
                >- (CCONTR_TAC >>
                    ‘N2Ab = N2Bb’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LReceive spB dB rpB’,
                                            ‘N1b’,‘conf’] >>
                    fs[net_wf_def])
                >- (qexists_tac ‘N1a’ >>
                    fs[net_wf_def,wf_label_def,compat_labels_def] >>
                    ‘net_has_node N1b rpA ∧ net_has_node N1b rpB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_receive_cond])) >>
          ‘∃N3b.
            trans conf N2Ab (LReceive spB dB rpB) N3b ∧
            trans conf N2Bb (LReceive spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[]
                >- (CCONTR_TAC >>
                    ‘N2Ab = N2Bb’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LReceive spB dB rpB’,
                                            ‘N1b’,‘conf’] >>
                    fs[net_wf_def])
                >- metis_tac[send_gen_compat,net_wf_def]
                >- (qexists_tac ‘N1b’ >>
                    fs[net_wf_def,wf_label_def,compat_labels_def] >>
                    ‘net_has_node N1a spA ∧ net_has_node N1a spB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_send_cond])) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Internal Comms (TO RIGHT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend spA dA rpA) N2Aa’,
                  ‘trans conf N1b (LSend spB dB rpB) N2Bb’] >>
          ‘∃N3a.
            trans conf N2Aa (LReceive spB dB rpB) N3a ∧
            trans conf N2Ba (LSend spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b rpA ∧ net_has_node N1b spB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          ‘∃N3b.
            trans conf N2Ab (LSend spB dB rpB) N3b ∧
            trans conf N2Bb (LReceive spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def] >>
                ‘net_has_node N1a spA ∧ net_has_node N1a rpB’
                  suffices_by metis_tac[DISJOINT_SYM,
                                        DISJOINT_ALT,
                                        IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO RIGHT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend spA dA rpA) N2Aa’,
                  ‘trans conf N1b (LSend spB dB rpB) N2Bb’] >>
          ‘∃N3a.
            trans conf N2Aa (LReceive spB dB rpB) N3a ∧
            trans conf N2Ba (LSend spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b rpA ∧ net_has_node N1b spB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          ‘∃N3b.
            trans conf N2Ab (LSend spB dB rpB) N3b ∧
            trans conf N2Bb (LReceive spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def] >>
                ‘net_has_node N1a spA ∧ net_has_node N1a rpB’
                  suffices_by metis_tac[DISJOINT_SYM,
                                        DISJOINT_ALT,
                                        IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Internal Comms (TO RIGHT) / Parallel Embedded Behaviour (LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N1b) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LSend sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO RIGHT) / Parallel Embedded Behaviour (LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N1b) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LSend sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Internal Comms (TO RIGHT) / Parallel Embedded Behaviour (RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N1a N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LReceive sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO RIGHT) / Parallel Embedded Behaviour (LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N1a N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LReceive sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Internal Comms (TO LEFT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive spA dA rpA) N2Aa’,
                  ‘trans conf N1a (LSend spB dB rpB) N2Ba’] >>
          ‘∃N3a.
            trans conf N2Aa (LSend spB dB rpB) N3a ∧
            trans conf N2Ba (LReceive spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b spA ∧ net_has_node N1b rpB’
                  suffices_by metis_tac[DISJOINT_SYM,
                                        DISJOINT_ALT,
                                        IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          ‘∃N3b.
            trans conf N2Ab (LReceive spB dB rpB) N3b ∧
            trans conf N2Bb (LSend spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def] >>
                ‘net_has_node N1a rpA ∧ net_has_node N1a spB’
                  suffices_by metis_tac[DISJOINT_SYM,
                                        DISJOINT_ALT,
                                        IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO LEFT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive spA dA rpA) N2Aa’,
                  ‘trans conf N1a (LSend spB dB rpB) N2Ba’] >>
          ‘∃N3a.
            trans conf N2Aa (LSend spB dB rpB) N3a ∧
            trans conf N2Ba (LReceive spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b spA ∧ net_has_node N1b rpB’
                  suffices_by metis_tac[DISJOINT_SYM,
                                        DISJOINT_ALT,
                                        IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          ‘∃N3b.
            trans conf N2Ab (LReceive spB dB rpB) N3b ∧
            trans conf N2Bb (LSend spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def] >>
                ‘net_has_node N1a rpA ∧ net_has_node N1a spB’
                  suffices_by metis_tac[DISJOINT_SYM,
                                        DISJOINT_ALT,
                                        IN_APP] >>
                metis_tac[trans_send_cond,trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Internal Comms (TO LEFT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive spA dA rpA) N2Aa’,
                  ‘trans conf N1a (LReceive spB dB rpB) N2Ba’] >>
          ‘∃N3a.
            trans conf N2Aa (LReceive spB dB rpB) N3a ∧
            trans conf N2Ba (LReceive spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[]
                >- (CCONTR_TAC >>
                    ‘N2Aa = N2Ba’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LReceive spB dB rpB’,
                                            ‘N1a’,‘conf’] >>
                    fs[net_wf_def])
                >- metis_tac[send_gen_compat,net_wf_def]
                >- (qexists_tac ‘N1a’ >>
                    fs[net_wf_def,wf_label_def] >>
                    ‘net_has_node N1b spA ∧ net_has_node N1b spB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_send_cond])) >>
          ‘∃N3b.
            trans conf N2Ab (LSend spB dB rpB) N3b ∧
            trans conf N2Bb (LSend spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def]
                >- (CCONTR_TAC >>
                    ‘N2Aa = N2Ba’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LReceive spB dB rpB’,
                                            ‘N1a’,‘conf’] >>
                    fs[net_wf_def])
                >- (qexists_tac ‘N1b’ >>
                    fs[net_wf_def,wf_label_def,compat_labels_def] >>
                    ‘net_has_node N1a rpA ∧ net_has_node N1a rpB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_receive_cond])) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO LEFT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive spA dA rpA) N2Aa’,
                  ‘trans conf N1a (LReceive spB dB rpB) N2Ba’] >>
          ‘∃N3a.
            trans conf N2Aa (LReceive spB dB rpB) N3a ∧
            trans conf N2Ba (LReceive spA dA rpA) N3a’
            by (irule trans_diff_diamond >>
                rw[]
                >- (CCONTR_TAC >>
                    ‘N2Ab = N2Bb’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LSend spB dB rpB’,
                                            ‘N1b’,‘conf’] >>
                    fs[net_wf_def])
                >- metis_tac[send_gen_compat,net_wf_def]
                >- (qexists_tac ‘N1a’ >>
                    fs[net_wf_def,wf_label_def] >>
                    ‘net_has_node N1b spA ∧ net_has_node N1b spB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_send_cond])) >>
          ‘∃N3b.
            trans conf N2Ab (LSend spB dB rpB) N3b ∧
            trans conf N2Bb (LSend spA dA rpA) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def]
                >- (CCONTR_TAC >>
                    ‘N2Ab = N2Bb’
                      suffices_by rw[] >>
                    irule trans_notau_functional >>
                    MAP_EVERY qexists_tac [‘LSend spB dB rpB’,
                                            ‘N1b’,‘conf’] >>
                    fs[net_wf_def])
                >- (qexists_tac ‘N1b’ >>
                    fs[net_wf_def,wf_label_def,compat_labels_def] >>
                    ‘net_has_node N1a rpA ∧ net_has_node N1a rpB’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                    metis_tac[trans_receive_cond])) >>
          qexists_tac ‘NPar N3a N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Internal Comms (TO LEFT) / Parallel Embedded Behaviour (LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N1b) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LReceive sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO LEFT) / Parallel Embedded Behaviour (LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N2Ba N1b) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LReceive sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Internal Comms (TO LEFT) / Parallel Embedded Behaviour (RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N1a N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LSend sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Internal Comms (TO LEFT) / Parallel Embedded Behaviour (RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N2Ab) LTau _ ∧
                   trans conf (NPar N1a N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LSend sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Parallel Embedded Behaviour (LEFT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N2Ba N1b) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LSend sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Parallel Embedded Behaviour (LEFT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N2Ba N1b) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LSend sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Parallel Embedded Behaviour (LEFT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N2Ba N1b) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LReceive sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Parallel Embedded Behaviour (LEFT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N2Ba N1b) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba (LReceive sp d rp) N3a’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1a’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1b sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N3a N2Ab’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Parallel Embedded Behaviour (LEFT) / Parallel Embedded Behaviour (LEFT) *)
      >- (rename [‘trans conf (NPar N2Aa N1b) LTau _ ∧
                   trans conf (NPar N2Ba N1b) LTau _’,
                  ‘net_wf (NPar N1a N1b)’] >>
          ‘∃N3a.
            trans conf N2Aa LTau N3a ∧
            trans conf N2Ba LTau N3a’
            by metis_tac[net_wf_def] >>
          qexists_tac ‘NPar N3a N1b’ >>
          metis_tac[trans_rules])
      (* Note: SECOND DIFF of dual parallel embedded left behaviour not possible! *)
      (* (FIRST DIFF) Parallel Embedded Behaviour (LEFT) / Parallel Embedded Behaviour (RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N1b) LTau _ ∧
                   trans conf (NPar N1a N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’] >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Parallel Embedded Behaviour (LEFT) / Parallel Embedded Behaviour (RIGHT) *)
      >- (rename [‘trans conf (NPar N2Aa N1b) LTau _ ∧
                   trans conf (NPar N1a N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’] >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Parallel Embedded Behaviour (RIGHT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N1a N2Bb) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LReceive sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Parallel Embedded Behaviour (RIGHT) / Internal Comms (TO RIGHT) *)
      >- (rename [‘trans conf (NPar N1a N2Bb) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _ ’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LSend sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LReceive sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a sp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_send_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Parallel Embedded Behaviour (RIGHT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N1a N2Bb) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _ ’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LSend sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Parallel Embedded Behaviour (RIGHT) / Internal Comms (TO LEFT) *)
      >- (rename [‘trans conf (NPar N1a N2Bb) LTau _ ∧
                   trans conf (NPar N2Aa N2Ab) LTau _ ’,
                  ‘net_wf (NPar N1a N1b)’,
                  ‘trans conf N1a (LReceive sp d rp) N2Aa’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb (LSend sp d rp) N3b’
            by (irule trans_diff_diamond >>
                rw[compat_labels_def] >>
                qexists_tac ‘N1b’ >>
                fs[net_wf_def,wf_label_def,compat_labels_def] >>
                ‘net_has_node N1a rp’
                      suffices_by metis_tac[DISJOINT_SYM,
                                            DISJOINT_ALT,
                                            IN_APP] >>
                metis_tac[trans_receive_cond]) >>
          qexists_tac ‘NPar N2Aa N3b’ >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Parallel Embedded Behaviour (RIGHT) / Parallel Embedded Behaviour (LEFT) *)
      >- (rename [‘trans conf (NPar N1a N2Bb) LTau _ ∧
                   trans conf (NPar N2Aa N1b) LTau _’,
                  ‘net_wf (NPar N1a N1b)’] >>
          metis_tac[trans_rules])
      (* (SECOND DIFF) Parallel Embedded Behaviour (LEFT) / Parallel Embedded Behaviour (RIGHT) *)
      >- (rename [‘trans conf (NPar N1a N2Bb) LTau _ ∧
                   trans conf (NPar N2Aa N1b) LTau _’,
                  ‘net_wf (NPar N1a N1b)’] >>
          metis_tac[trans_rules])
      (* (FIRST DIFF) Parallel Embedded Behaviour (RIGHT) / Parallel Embedded Behaviour (RIGHT) *)
      >- (rename [‘trans conf (NPar N1a N2Ab) LTau _ ∧
                   trans conf (NPar N1a N2Bb) LTau _’,
                  ‘net_wf (NPar N1a N1b)’] >>
          ‘∃N3b.
            trans conf N2Ab LTau N3b ∧
            trans conf N2Bb LTau N3b’
            by metis_tac[net_wf_def] >>
          qexists_tac ‘NPar N1a N3b’ >>
          metis_tac[trans_rules])
      (* Note: SECOND DIFF of dual parallel embedded right behaviour not possible! *)
      )
  (* NEndpoint case *)
  >- (rw[] >>
      qpat_x_assum ‘trans _ _ _ N2A’
                  (fn x => strip_assume_tac(REWRITE_RULE [Once trans_cases] x)) >>
      fs[] >> rw[] >> fs[] >>
      qpat_x_assum ‘trans _ _ _ N2B’
                  (fn x => strip_assume_tac(REWRITE_RULE [Once trans_cases] x)) >>
      fs[] >> rw[] >> fs[] >>
      metis_tac[final_inter_mutexc])
QED

(*  General Reflexive Confluence Result*)
Theorem trans_diamond:
  ∀conf N1 LA N2A LB N2B.
    net_wf N1 ∧
    wf_label N1 LA ∧
    wf_label N1 LB ∧
    compat_labels LA LB ∧
    trans conf N1 LA N2A ∧
    trans conf N1 LB N2B ⇒
    ∃N3.
      RC (λn1 n2. trans conf n1 LB n2) N2A N3 ∧
      RC (λn1 n2. trans conf n1 LA n2) N2B N3
Proof
  rw[] >>
  Cases_on ‘LA = LB’
  >- (Cases_on ‘LA = LTau’ >> rw[RC_DEF]
      >- (rw[RC_DEF] >>
          metis_tac[trans_samelab_tau_difout_diamond])
      >- metis_tac[RC_DEF,trans_notau_functional])
  >- (rw[RC_DEF] >> metis_tac[trans_diff_diamond])
QED

(* Makes sure a network has every message queue empty (payload version) *)
Definition empty_q_def:
  empty_q NNil = T
∧ empty_q (NPar n1 n2)     = (empty_q n1 ∧ empty_q n2)
∧ empty_q (NEndpoint _ s _) = (s.queues = FEMPTY)
End

(* trans preserves the structure of the network *)
Theorem trans_struct_pres_NPar:
  ∀conf n L l r.
   trans conf (NPar l r) L n
   ⇒ ∃ l' r'. n = NPar l' r'
Proof
  rw [Once trans_cases]
QED

(* trans preserves the structure of the network *)
Theorem trans_struct_pres_NPar_NEndpoint:
  ∀conf p s c n L n'.
   trans conf (NPar (NEndpoint p s c) n) L n'
   ⇒ ∃ s' c' n''. n' = NPar (NEndpoint p s' c') n''
Proof
  rw []
  \\ pop_assum (ASSUME_TAC o ONCE_REWRITE_RULE [trans_cases])
  \\ fs []
  \\ qpat_x_assum ‘trans conf (NEndpoint _ _ _) _ _’
                  (ASSUME_TAC o ONCE_REWRITE_RULE [trans_cases])
  \\ fs []
QED

(* trans preserves the structure of the network *)
Theorem trans_struct_pres_NEnpoint:
  ∀conf p s c n L n'.
   trans conf (NEndpoint p s c) L n'
   ⇒ ∃ s' c'. n' = NEndpoint p s' c'
Proof
  rw []
  \\ pop_assum (ASSUME_TAC o ONCE_REWRITE_RULE [trans_cases])
  \\ fs []
QED

val (junkcong_rules, junkcong_ind, junkcong_cases) = Hol_reln `
  (* Reflexive *)
  (∀fvs n:payloadLang$network. junkcong fvs n n)

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
    ⇒ junkcong fvs (NEndpoint p <|bindings := b; queues := q|> e)
                    (NEndpoint p <|bindings := b |+ (v,d); queues := q|> e)`,
 rpt strip_tac
 >> qmatch_goalsub_abbrev_tac `junkcong _ (NEndpoint _ a1 _) (NEndpoint _ a2 _)`
 >> `a2 = a1 with bindings := a1.bindings |+ (v,d)`
     by(unabbrev_all_tac >> simp[])
 >> rveq
 >> match_mp_tac junkcong_add_junk >> simp[]);

val junkcong_add_junk''' = Q.store_thm("junkcong_add_junk'''",
  `∀p s q e v fvs d.
     v ∈ fvs ∧ ¬MEM v (free_var_names_endpoint e) ⇒
     junkcong fvs (NEndpoint p (s with queues := q) e)
     (NEndpoint p (s with <|bindings := s.bindings |+ (v,d); queues := q|>) e)`,
  rpt strip_tac
  >> qpat_abbrev_tac `a1 = s with queues := q`
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
      >> `s with bindings := s.bindings = s` by fs[payloadLangTheory.state_component_equality]
      >> fs[FUPDATE_ELIM] >> match_mp_tac junkcong_sym >> first_x_assum ACCEPT_TAC)
  >- (fs[DOMSUB_NOT_IN_DOM]
      >> match_mp_tac junkcong_refl_IMP >> simp[payloadLangTheory.state_component_equality]));

val junkcong_sym_eq = Q.store_thm("junkcong_sym_eq",
`∀fvs p q. junkcong fvs p q = junkcong fvs q p`,metis_tac[junkcong_sym]);

val junkcong_trans_eq = Q.store_thm("junkcong_trans_eq",
  `∀fvs p1 q1.
     junkcong fvs p1 q1
     ⇒ ∀ conf alpha p2 q2.
            ((trans conf p1 alpha p2 ⇒ (∃q2. trans conf q1 alpha q2 ∧ junkcong fvs p2 q2))
         ∧ (trans conf q1 alpha q2 ⇒ (∃p2. trans conf p1 alpha p2 ∧ junkcong fvs p2 q2)))`,
  ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- metis_tac[junkcong_rules]
  >- (* junkcong_add_junk *)
     (qpat_x_assum `trans _ _ _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemTheory.trans_cases])
      >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 a2 a3)`
             >> qexists_tac `NEndpoint a1 (a2 with bindings := a2.bindings |+ (v,d)) a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS payloadSemTheory.trans_rules)
                 >> fs[FLOOKUP_UPDATE,free_var_names_endpoint_def])
             >- (`¬MEM v (free_var_names_endpoint a3)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> fs[free_var_names_endpoint_def] >> metis_tac[junkcong_rules]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with queues := a3) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with <|queues := a3; bindings := a2.bindings |+ (v,d)|>) a4`
             >> conj_tac
             >- (PURE_ONCE_REWRITE_TAC [payloadLangTheory.state_fupdcanon]
                 >> qmatch_goalsub_abbrev_tac `trans _ (NEndpoint _ a5 _)`
                 >> `a2 with <|bindings := a2.bindings |+ (v,d); queues := a3|>
                     = a5 with queues := a3` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> qunabbrev_tac `a3`
                 >> `a2.queues = a5.queues` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> simp[])
             >- (imp_res_tac junkcong_add_junk
                 >> pop_assum(qspec_then `a2 with queues := a3` assume_tac)
                 >> fs[]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1
                                                                <|bindings := a2;
                                                                  queues := a3|>
                                                                a4)`
             >> qexists_tac `NEndpoint a1 <|bindings := if v = v' then a2
                                                        else a2 |+ (v,d); queues := a3|> a4`
             >> conj_tac
             >- (IF_CASES_TAC
                 >> unabbrev_all_tac
                 >> `s.queues = (s with bindings := s.bindings |+ (v,d)).queues` by simp[]
                 >> pop_assum(fn thm => FULL_SIMP_TAC bool_ss [Once thm])
                 >> imp_res_tac trans_dequeue_intermediate_payload
                 >> imp_res_tac trans_dequeue_last_payload
                 >> first_x_assum(qspec_then `v'` assume_tac)
                 >> rveq
                 >> fs[Once FUPDATE_COMMUTES])
             >- (IF_CASES_TAC
                 >- metis_tac[junkcong_rules]
                 >> `¬MEM v (free_var_names_endpoint a4)`
                     by(unabbrev_all_tac >> fs[free_var_names_endpoint_def,MEM_FILTER])
                 >> metis_tac[junkcong_add_junk'']))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with queues := a3) a4)`
             >> qexists_tac `NEndpoint a1 (<|queues := a3;
                                             bindings := a2.bindings |+ (v,d)|>) a4`
             >> conj_tac
             >- (PURE_ONCE_REWRITE_TAC [payloadLangTheory.state_fupdcanon]
                 >> qmatch_goalsub_abbrev_tac `trans _ (NEndpoint _ a5 _)`
                 >> `<|bindings := a2.bindings |+ (v,d); queues := a3|>
                     = a5 with queues := a3` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> qunabbrev_tac `a4`
                 >> qunabbrev_tac `a3`
                 >> `a2.queues = a5.queues` by(unabbrev_all_tac >> simp[])
                 >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> unabbrev_all_tac >> simp[])
             >- (`¬MEM v (free_var_names_endpoint a4)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> imp_res_tac junkcong_add_junk
                 >> rpt(first_x_assum(qspec_then `a2 with queues := a3` assume_tac ))
                 >> fs[]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with bindings := a3) a4)`
             >> qexists_tac `NEndpoint a1 (a2 with bindings := if v = v' then a3
                                                               else a3|+ (v,d)) a4`
             >> conj_tac
             >- (IF_CASES_TAC
                 >> unabbrev_all_tac >> fs[free_var_names_endpoint_def,MEM_FILTER]
                 >> `EVERY IS_SOME (MAP (FLOOKUP ((s with bindings := s.bindings |+ (v,d)).bindings)) vl)`
                     by(fs[EVERY_MAP,FLOOKUP_UPDATE,EVERY_MEM] >> rw[])
                 >> drule trans_let >> fs[] >> disch_then(qspecl_then [‘conf’,`v'`] assume_tac)
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
      >> qpat_x_assum `trans _ _ _ _` (assume_tac
                                       o REWRITE_RULE [Once payloadSemTheory.trans_cases])
      >> fs[] >> rveq
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs (NEndpoint a1 (a2 with bindings := _) a3)`
             >> qexists_tac `NEndpoint a1 a2 a3`
             >> conj_tac
             >- (unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS payloadSemTheory.trans_rules)
                 >> fs[FLOOKUP_UPDATE,free_var_names_endpoint_def] >> rfs[])
             >- (`¬MEM v (free_var_names_endpoint a3)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> fs[free_var_names_endpoint_def] >> metis_tac[junkcong_rules]))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs
                                                (NEndpoint a1
                                                           <|bindings := a2 |+ _ |+ (a3,a4);
                                                             queues := a5|> a6)`
             >> qexists_tac `NEndpoint a1 (s with <|queues := a5; bindings := a2 |+ (a3,a4)|>) a6`
             >> conj_tac
             >- (unabbrev_all_tac >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> simp[])
             >- (Cases_on `v = a3` >> fs[Once FUPDATE_COMMUTES]
                 >> fs[free_var_names_endpoint_def,MEM_FILTER]
                 >> metis_tac[junkcong_rules,junkcong_add_junk']))
      >> TRY(qmatch_goalsub_abbrev_tac `junkcong fvs
                                                (NEndpoint a1
                                                           <|bindings := a2 |+ (v,d);
                                                             queues := a3|> a4)`
             >> qexists_tac `NEndpoint a1 (s with queues := a3) a4`
             >> conj_tac
             >- (PURE_ONCE_REWRITE_TAC [payloadLangTheory.state_fupdcanon]
                 >> unabbrev_all_tac
                 >> MAP_FIRST match_mp_tac (CONJUNCTS trans_rules)
                 >> simp[])
             >- (`¬MEM v (free_var_names_endpoint a4)`
                   by(unabbrev_all_tac >> fs[free_var_names_endpoint_def])
                 >> imp_res_tac junkcong_add_junk
                 >> rpt(first_x_assum(qspec_then `s with queues := a3` assume_tac))
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
     (qpat_x_assum `trans _ (NPar _ _) _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[junkcong_rules])
  >- (* par-r *)
     (qpat_x_assum `trans _ (NPar _ _) _ _` (assume_tac
                                    o REWRITE_RULE [Once payloadSemTheory.trans_cases])
      >> fs[] >> rveq
      >> EVERY_ASSUM imp_res_tac
      >> imp_res_tac trans_com_l
      >> imp_res_tac trans_com_r
      >> imp_res_tac trans_par_l
      >> imp_res_tac trans_par_r
      >> metis_tac[junkcong_rules]));

val junkcong_reduction_eq = Q.store_thm("junkcong_reduction_eq",
  `∀conf fvs p1 q1.
     junkcong fvs p1 q1
     ⇒ ∀ p2 q2.
         (((reduction conf)^* p1 p2 ⇒ (∃q2. (reduction conf)^* q1 q2 ∧ junkcong fvs p2 q2))
         ∧ ((reduction conf)^* q1 q2 ⇒ (∃p2. (reduction conf)^* p1 p2 ∧ junkcong fvs p2 q2)))`,
  rw []
  >- (last_x_assum mp_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`q2`,`q1`,`fvs`]
      \\ first_x_assum mp_tac
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) [`p2`,`p1`]
      \\ ho_match_mp_tac RTC_ind \\ rw []
      >- (qexists_tac ‘q1’ \\ fs [junkcong_rules])
      \\ fs [reduction_def]
      \\ drule_then (qspecl_then [‘conf’,‘LTau’,‘p1'’,‘q1'’] assume_tac) junkcong_trans_eq
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
  \\ drule_then (qspecl_then [‘conf’,‘LTau’,‘p1'’,‘q1'’] assume_tac) junkcong_trans_eq
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
   junkcong fvs (NEndpoint p1 s1 e1) (NEndpoint p1 s2 e1) ==> s1.queues = s2.queues`,
  `!fvs n1 n2.
    junkcong fvs n1 n2
    ==> (!p1 s1 s2 e1. n1 = NEndpoint p1 s1 e1 /\ n2 = NEndpoint p1 s2 e1
          ==> s1.queues = s2.queues)`
    suffices_by metis_tac[]
  >> ho_match_mp_tac junkcong_strongind
  >> rpt strip_tac >> fs[] >> rveq
  >> simp[] >> metis_tac [junkcong_rules,junkcong_endpoint_rel_endpoint]);

val junkcong_endpoints = Q.store_thm("junkcong_endpoints",
  `!fvs n1 n2. junkcong fvs n1 n2 ==> MAP FST (endpoints n1) = MAP FST (endpoints n2)`,
  ho_match_mp_tac junkcong_ind
  >> rpt strip_tac >> fs[endpoints_def]);

val junkcong_trans_pres = Q.store_thm("junkcong_trans_pres",
  `∀conf p1 q1 fv alpha p2.
     junkcong fv p1 q1 ∧ trans conf p1 alpha p2
     ⇒ ∃q2. trans conf q1 alpha q2 ∧ junkcong fv p2 q2`,
  metis_tac[junkcong_trans_eq])

val junkcong_reduction_pres = Q.store_thm("junkcong_reduction_pres",
  `∀conf p1 q1 fv alpha p2.
     junkcong fv p1 q1 ∧ (reduction conf)^* p1 p2
     ⇒ ∃q2. (reduction conf)^* q1 q2 ∧ junkcong fv p2 q2`,
  metis_tac[junkcong_reduction_eq])

val _ = export_theory ();
