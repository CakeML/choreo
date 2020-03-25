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

val endpoints_def = Define `
   (endpoints NNil = [])
/\ (endpoints (NEndpoint p1 s e1) = [(p1,s,e1)])
/\ (endpoints (NPar n1 n2) = endpoints n1 ++ endpoints n2)`

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

val _ = export_theory ();
