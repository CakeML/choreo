open  HolKernel
      boolLib
      bossLib
      relationTheory;

val _ = new_theory "confluence";

(* DIAMOND PROPERTY PROOFS *)
(* Basic diamond Property gives diamond property with
   one side switched to reflexive, and transitive
   closure *)
Theorem diam_to_srtc_diam:
  ∀tsA tsB wfP.
    (* ASSUMPTIONS *)
    (* 1. wfP is preserved by tsA and tsB *)
    (∀x y.
      wfP x ∧ tsA x y ⇒ wfP y) ∧
    (∀x y.
      wfP x ∧ tsB x y ⇒ wfP y) ∧
    (* 2. tsA and tsB have diamond on wfP states *)
    (∀S1 S2A S2B.
      wfP S1 ∧
      tsA S1 S2A ∧
      tsB S1 S2B ⇒
      ∃S3.
        tsB S2A S3 ∧
        tsA S2B S3) ⇒
    (* CONCLUSION *)
    (* tsA and tsB have semi-RTC diamond on wfP states *)
    (∀S1 S2A S2B.
      wfP S1 ∧
      RTC tsA S1 S2A ∧
      tsB S1 S2B ⇒
      ∃S3.
        tsB S2A S3 ∧
        RTC tsA S2B S3)
Proof
  rw[] >>
  pop_assum mp_tac >>
  qpat_x_assum ‘wfP S1’ mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘S1’,‘S2A’,‘S2B’] >>
  Induct_on ‘RTC’ >> rw[]
  >- metis_tac[RC_DEF,RTC_REFL] >>
  rename [‘wfP S1’,‘tsA S1 SI’,‘RTC tsA SI S2A’,‘tsB S1 S2B’] >>
  ntac 2 (last_x_assum assume_tac) >>
  last_x_assum (drule_all_then strip_assume_tac) >>
  ‘wfP SI’
    by metis_tac[] >>
  fs[] >>
  last_x_assum (drule_all_then strip_assume_tac) >>
  metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SINGLE]
QED

(* Reflexive closure diamond property gives diamond property with
   one side switched to reflexive, and transitive
   closure and the other still reflexive closure *)
Theorem rc_diam_to_srtc_diam:
  ∀tsA tsB wfP.
    (* ASSUMPTIONS *)
    (* 1. wfP is preserved by tsA and tsB *)
    (∀x y.
      wfP x ∧ tsA x y ⇒ wfP y) ∧
    (∀x y.
      wfP x ∧ tsB x y ⇒ wfP y) ∧
    (* 2. tsA and tsB have RC diamond on wfP states *)
    (∀S1 S2A S2B.
      wfP S1 ∧
      tsA S1 S2A ∧
      tsB S1 S2B ⇒
      ∃S3.
        RC tsB S2A S3 ∧
        RC tsA S2B S3) ⇒
    (* CONCLUSION *)
    (* tsA and tsB have semi-RTC diamond on wfP states *)
    (∀S1 S2A S2B.
      wfP S1 ∧
      RTC tsA S1 S2A ∧
      tsB S1 S2B ⇒
      ∃S3.
        RC tsB S2A S3 ∧
        RTC tsA S2B S3)
Proof
  rw[] >>
  pop_assum mp_tac >>
  qpat_x_assum ‘wfP S1’ mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘S1’,‘S2A’,‘S2B’] >>
  Induct_on ‘RTC’ >> rw[]
  >- metis_tac[RC_DEF,RTC_REFL] >>
  rename[‘tsA S1 SI’,‘tsB S1 S2B’] >>
  ntac 2 (last_x_assum assume_tac) >>
  last_x_assum (drule_all_then strip_assume_tac) >>
  rpt (qpat_x_assum ‘RC _ _ _’ (assume_tac o REWRITE_RULE [RC_DEF])) >>
  fs[] >> fs[] >>
  metis_tac[RC_DEF,RTC_TRANSITIVE,transitive_def,RTC_SINGLE]
QED

(* Reflexive closure diamond property gives complete
   reflexive, and transitive closure diamond property. *)
Theorem rc_diam_to_rtc_diam:
  ∀tsA tsB wfP.
    (* ASSUMPTIONS *)
    (* 1. wfP is preserved by tsA and tsB *)
    (∀x y.
      wfP x ∧ tsA x y ⇒ wfP y) ∧
    (∀x y.
      wfP x ∧ tsB x y ⇒ wfP y) ∧
    (* 2. tsA and tsB have RC diamond on wfP states *)
    (∀S1 S2A S2B.
      wfP S1 ∧
      tsA S1 S2A ∧
      tsB S1 S2B ⇒
      ∃S3.
        RC tsB S2A S3 ∧
        RC tsA S2B S3) ⇒
    (* CONCLUSION *)
    (* tsA and tsB have RTC diamond on wfP states*)
    (∀S1 S2A S2B.
      wfP S1 ∧
      RTC tsA S1 S2A ∧
      RTC tsB S1 S2B ⇒
      ∃S3.
        RTC tsB S2A S3 ∧
        RTC tsA S2B S3)
Proof
  ntac 4 strip_tac >>
  qspecl_then [‘tsA’,‘tsB’,‘wfP’] assume_tac rc_diam_to_srtc_diam >>
  qmatch_asmsub_abbrev_tac ‘A ⇒ B’ >>
  ‘B’
    by (‘A’ suffices_by rw[] >> 
        qunabbrev_tac ‘A’ >> metis_tac[]) >>
  qpat_x_assum ‘A ⇒ B’ (K ALL_TAC) >>
  MAP_EVERY qunabbrev_tac [‘A’,‘B’] >>
  ntac 2 (last_x_assum assume_tac) >>
  last_x_assum (K ALL_TAC) >>
  qspecl_then [‘tsB’,‘RTC tsA’,‘wfP’] assume_tac rc_diam_to_srtc_diam >>
  ‘RC (RTC tsA) = RTC tsA’
    by (rw[FUN_EQ_THM,RC_DEF] >>
        ‘∀a b. (a = b ∨ RTC tsA a b) ⇔ (RTC tsA a b)’
          by (‘∀a b. a = b ⇒ RTC tsA a b’
                suffices_by metis_tac[] >>
              metis_tac[RTC_REFL]) >>
        fs[]) >>
  pop_assum (fn x => pop_assum (assume_tac o REWRITE_RULE[x])) >>
  qmatch_asmsub_abbrev_tac ‘A ⇒ B’ >>
  ‘B’
    suffices_by (qunabbrev_tac ‘B’ >> rw[] >>
                 metis_tac[]) >>
  ‘A’
    suffices_by fs[] >>
  qunabbrev_tac ‘A’ >>
  ntac 2 (pop_assum (K ALL_TAC)) >>
  rw[]
  >- metis_tac[]
  >- (qpat_x_assum ‘wfP x’ mp_tac >>
      pop_assum mp_tac >>
      MAP_EVERY qid_spec_tac [‘x’,‘y’] >>
      Induct_on ‘RTC’ >>
      metis_tac[])
  >- metis_tac[]
QED

val _ = export_theory ();
