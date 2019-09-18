open HolKernel boolLib Parse bossLib;
open relationTheory
	 pred_setTheory;
open payloadLangTheory
     payloadSemanticsTheory;

val _ = new_theory "payloadProps";

(* BASIC THEOREMS *)
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
                <|queues := sq.queues |+ (sp2,tln);
                  bindings := sq.bindings |+ (sv2,FLAT (SNOC (unpad dr) ds2)) |>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[]
                >- (rfs[] >> rw[listTheory.SNOC_APPEND])
                >- (rw[finite_mapTheory.FUPDATE_COMMUTES])) >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules])
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint c s0 e) _ (NEndpoint c s1 e)’ >>
          ‘s1 = s0 with queues := qpush s0.queues sp d’
            by (qunabbrev_tac ‘s0’ >> qunabbrev_tac ‘s1’ >> rw[]) >>
          rw[] >> metis_tac[trans_rules]))
  (* LReceive/LTau (Receive intermediate)  *)
  >- (rename [‘NEndpoint c (s with queues := _) (Receive sp2 sv2 ds2 e)’,
              ‘LReceive sp d c’,‘qlk s.queues sp2 = dr::tl’] >>
      qexists_tac ‘NEndpoint c (s with queues := qpush (s.queues |+ (sp2,tl)) sp d)
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
                <|queues := sq.queues |+ (sp2,tln)|>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[]
                >- (rfs[] >> rw[listTheory.SNOC_APPEND])
                >- (rw[finite_mapTheory.FUPDATE_COMMUTES])) >>
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
      qexists_tac ‘NEndpoint c <|bindings := fb; queues := qpush bfq sp d|> e’ >>
      rw[]
      >- (qmatch_goalsub_abbrev_tac ‘trans _ (NEndpoint c s0 e) _ (NEndpoint c s1 e)’ >>
          ‘s1 = s0 with queues := qpush s0.queues sp d’
            by (qunabbrev_tac ‘s0’ >> qunabbrev_tac ‘s1’ >> rw[]) >>
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
                <|queues := sq.queues |+ (sp2,tln);
                  bindings := sq.bindings |+ (sv2,FLAT (SNOC (unpad dr) ds2)) |>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[]
                >- (rfs[] >> rw[listTheory.SNOC_APPEND])
                >- (rw[finite_mapTheory.FUPDATE_COMMUTES])) >>
          first_x_assum SUBST1_TAC >>
          metis_tac[trans_rules]))
  (* LTau (Receive intermediate)/LReceive  *)
  >- (rename [‘NEndpoint c (s with queues := _) (Receive sp2 sv2 (SNOC (unpad dr) ds2) e)’,
              ‘LReceive sp d c’,‘qlk s.queues sp2 = dr::tl’] >>
      qexists_tac ‘NEndpoint c (s with queues := qpush (s.queues |+ (sp2,tl)) sp d)
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
                <|queues := sq.queues |+ (sp2,tln)|>’
            by (qunabbrev_tac ‘sq’ >> qunabbrev_tac ‘ns’ >>
                fs[qpush_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE] >>
                Cases_on ‘sp = sp2’ >> fs[]
                >- (rfs[] >> rw[listTheory.SNOC_APPEND])
                >- (rw[finite_mapTheory.FUPDATE_COMMUTES])) >>
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


val _ = export_theory ();

