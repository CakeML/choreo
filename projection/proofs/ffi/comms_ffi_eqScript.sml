open HolKernel boolLib Parse bossLib;
open optionTheory
     relationTheory;
open ffiTheory;
open bisimulationTheory
     bisimulation_extTheory
     confluenceTheory
     payloadPropsTheory
     payloadSemanticsTheory
     payloadLangTheory
     comms_ffi_modelTheory
     comms_ffi_propsTheory
     comms_ffi_consTheory
     comms_ffi_commTheory;

val _ = new_theory "comms_ffi_eq";

(* FFI STATE EQUIVALENCE *)
(* Definition *)
Definition ffi_eq_def:
  ffi_eq conf = BISIM_REL (strans conf)
End

(* Basic equivalence property *)
Theorem ffi_eq_equivRel:
  ∀conf. equivalence (ffi_eq conf)
Proof
  rw [ffi_eq_def,BISIM_REL_IS_EQUIV_REL]
QED

(* Irrelevance if queues are similar *)
Theorem qsame_irrel_ffi_eq:
  ∀c q1 q2 N.
    qsame q1 q2 ⇒
    ffi_eq conf (c,q1,N) (c,q2,N)
Proof
  simp[ffi_eq_def,bi_is_BISIM_REL] >>
  ‘∀s1 s2.
    (λ(c1,q1,N1) (c2,q2,N2).
      c1 = c2 ∧
      N1 = N2 ∧
     qsame q1 q2) s1 s2 ⇒
    bi (strans conf) s1 s2’
    suffices_by (rw[] >> metis_tac[pairTheory.FORALL_PROD]) >>
  ho_match_mp_tac bi_coind >> rw[] >>
  rename1 ‘strans conf _ L sO’ >>
  MAP_EVERY PairCases_on [‘s1’,‘s2’,‘sO’] >>
  fs[] >> rw[] >> 
  last_x_assum mp_tac >> 
  pop_assum mp_tac >> rw[] >> Cases_on ‘L’ >>
  ‘sO0 = s10’
    by metis_tac[pairTheory.FST,strans_pres_pnum] >>
  fs[strans_send_equiv,strans_receive_equiv,pairTheory.EXISTS_PROD]
  >- (MAP_EVERY (drule_all_then strip_assume_tac)
                [qsame_irrel_active,
                 qsame_irrel_send,
                 qsame_irrel_internal] >>
      rename1 ‘input_trans conf _ (q2MA,_) _ (q2MB,_)’ >>
      ‘q2MA = q2MB’
        by fs[input_trans_def] >>
      rw[] >> metis_tac[])
  >- (MAP_EVERY (drule_all_then strip_assume_tac)
                [qsame_irrel_active,
                 qsame_irrel_receive] >>
      fs[] >>
      drule_all_then strip_assume_tac qsame_irrel_internal >>
      rw[] >> metis_tac[])
  >- (‘∀(x : word8 list |-> word8 list list) y. qsame x y ⇔ qsame y x’
        by (rw[qsame_def] >> metis_tac[]) >>
      rename1 ‘qsame A B’ >>
      ‘qsame B A’ by metis_tac[] >>
      MAP_EVERY (drule_all_then strip_assume_tac)
                [qsame_irrel_active,
                 qsame_irrel_send,
                 qsame_irrel_internal] >>
      rename1 ‘input_trans conf _ (q2MA,_) _ (q2MB,_)’ >>
      ‘q2MA = q2MB’
        by fs[input_trans_def] >>
      rw[] >> metis_tac[])
  >- (‘∀(x : word8 list |-> word8 list list) y. qsame x y ⇔ qsame y x’
        by (rw[qsame_def] >> metis_tac[]) >>
      rename1 ‘qsame A B’ >>
      ‘qsame B A’ by metis_tac[] >>
      MAP_EVERY (drule_all_then strip_assume_tac)
                [qsame_irrel_active,
                 qsame_irrel_receive] >>
      fs[] >>
      drule_all_then strip_assume_tac qsame_irrel_internal >>
      rw[] >> metis_tac[])
QED

(* DECONSTRUCTION PIECES EQUIVALENCE PRESERVATION *)
(* General Theorems *)
(* -- Equiv. irrel. gives equiv. pres. *)
Theorem equiv_irrel_pres:
  ∀ts.
    (* ASSUMPTIONS *)
    (* 1. RTC ts is irrelevant to equivalence *)
    (∀conf c q1 N1 q2 N2.
      ffi_wf (c,q1,N1) ∧
      RTC (ts conf c) (q1,N1) (q2,N2) ⇒
      ffi_eq conf (c,q1,N1) (c,q2,N2)) ⇒
    (* CONCLUSION *)
    (* RTC ts preserves equivalence *)
    (∀conf cA q1A N1A q2A N2A cB q1B N1B q2B N2B.
      ffi_wf (cA,q1A,N1A) ∧
      ffi_wf (cB,q1B,N1B) ∧
      ffi_eq conf (cA,q1A,N1A) (cB,q1B,N1B) ∧
      RTC (ts conf cA) (q1A,N1A) (q2A,N2A)       ∧
      RTC (ts conf cB) (q1B,N1B) (q2B,N2B)       ⇒
      ffi_eq conf (cA,q2A,N2A) (cB,q2B,N2B))
Proof
  rw[] >>
  metis_tac[ffi_eq_equivRel,equivalence_def,
                          transitive_def,symmetric_def]
QED

(* -- strans comm. + subset of active_trans gives equiv. pres. *)
Theorem equiv_irrel_cond:
  ∀ts.
    (* ASSUMPTIONS *)
    (* 1. ts is a subset of active_trans *)
    (∀conf c q1 N1 q2 N2.
      ts conf c (q1,N1) (q2,N2) ⇒
      active_trans conf c (q1,N1) (q2,N2)) ∧
    (* 2. RTC ts commutes with strans *)
    (∀conf c q1 N1 L q2S N2S q2T N2T.
      ffi_wf (c,q1,N1) ∧
      strans conf (c,q1,N1) L (c,q2S,N2S) ∧
      RTC (ts conf c) (q1,N1) (q2T,N2T) ⇒
      ∃q3 N3.
        RTC (ts conf c) (q2S,N2S) (q3,N3) ∧
        strans conf (c,q2T,N2T) L (c,q3,N3)) ⇒
    (* CONCLUSION *)
    (* RTC ts is irrelevant to equivalence *)
    (∀conf c q1 N1 q2 N2.
      ffi_wf (c,q1,N1) ∧
      RTC (ts conf c) (q1,N1) (q2,N2) ⇒
      ffi_eq conf (c,q1,N1) (c,q2,N2))
Proof
  ntac 3 strip_tac >>
  simp[ffi_eq_def,bi_is_BISIM_REL] >>
  gen_tac >>
  ‘∀s1 s2.
    (λ (c1,q1,N1) (c2,q2,N2).
      c1 = c ∧
      c2 = c ∧
      ffi_wf (c,q1,N1) ∧
      RTC (ts conf c) (q1,N1) (q2,N2)) s1 s2
    ⇒ bi (strans conf) s1 s2’
    suffices_by rw[] >>
  ho_match_mp_tac bi_coind >>
  rw[] >>
  PairCases_on ‘s1’ >> PairCases_on ‘s2’ >>
  fs[] >> rfs[]
  >- (rename [‘strans conf _ L s3’,
              ‘∃x. strans conf _ L x ∧
                   _ s3 x’] >>
      ‘FST s3 = c’
        by metis_tac[strans_pres_pnum,
                     pairTheory.FST] >>
      PairCases_on ‘s3’ >>
      fs[] >>
      pop_assum (K ALL_TAC) >>
      pop_assum mp_tac >>
      qpat_x_assum ‘ffi_wf (c,s11,s12)’ mp_tac >>
      pop_assum mp_tac >>
      qabbrev_tac ‘s1 = (s11,s12)’ >>
      qabbrev_tac ‘s2a = (s21,s22)’ >>
      qabbrev_tac ‘s2b = (s31,s32)’ >> 
      ntac 5 (pop_assum (K ALL_TAC)) >>
      MAP_EVERY qid_spec_tac [‘s2b’,‘s2a’,‘s1’] >>
      Induct_on ‘RTC’ >> rw[]
      >- (qexists_tac ‘(c,s2b)’ >> rw[] >>
          PairCases_on ‘s2b’ >> rw[] >>
          metis_tac[strans_pres_wf])
      >- (rename1 ‘ts conf c s1 si’ >>
          PairCases_on ‘s1’ >> PairCases_on ‘si’ >>
          PairCases_on ‘s2b’ >>
          ‘∃siM0 siM1. strans conf (c,si0,si1) L (c,siM0,siM1) ∧
                 RTC (ts conf c) (s2b0,s2b1) (siM0,siM1)’
            by metis_tac[RTC_SINGLE] >>
          ‘ffi_wf (c,si0,si1)’
            by metis_tac[active_trans_pres_wf,RTC_SINGLE] >>
          first_x_assum (drule_all_then strip_assume_tac) >>
          rename1 ‘strans conf (c,s2a) L s3’ >>
          qexists_tac ‘s3’ >>
          PairCases_on ‘s3’ >>
          fs[] >>
          metis_tac[strans_pres_wf,RTC_SINGLE,
                    RTC_TRANSITIVE,transitive_def]))
  >- (rename [‘strans conf _ L s3’,
              ‘∃x. strans conf _ L x ∧
                   _ x s3’] >>
      qexists_tac ‘s3’ >>
      ‘RTC (active_trans conf c) (s11,s12) (s21,s22)’
        suffices_by (‘FST s3 = c’
                        by metis_tac[strans_pres_pnum,
                                     pairTheory.FST] >>
                     PairCases_on ‘s3’ >>
                     fs[] >>
                     metis_tac[strans_pres_pnum,
                               strans_front_construct,
                               strans_pres_wf]) >>
      pop_assum (K ALL_TAC) >>
      qpat_x_assum ‘ffi_wf (c,s11,s12)’ mp_tac >>
      pop_assum mp_tac >>      
      qabbrev_tac ‘sa = (s11,s12)’ >>
      qabbrev_tac ‘sb = (s21,s22)’ >> 
      ntac 5 (pop_assum (K ALL_TAC)) >>
      MAP_EVERY qid_spec_tac [‘sb’,‘sa’] >>
      Induct_on ‘RTC’ >> rw[] >>
      rename1 ‘ts conf c sa si’ >>
      ‘active_trans conf c sa si’
        suffices_by (‘ffi_wf (c,si)’
                      by (MAP_EVERY PairCases_on [‘sa’,‘si’] >>
                          metis_tac[active_trans_pres_wf,RTC_SINGLE]) >>
                    metis_tac[RTC_SINGLE,RTC_TRANSITIVE,transitive_def]) >>
      PairCases_on ‘sa’ >> PairCases_on ‘si’ >> metis_tac[])
QED

(* Equivalence Preservation for Specific Pieces *)
(* -- Internal *)
(* -- -- Equivalence Irrelevance *)
Theorem internal_trans_equiv_irrel:
  ∀conf c q1 N1 q2 N2.
    ffi_wf (c,q1,N1) ∧
    RTC (internal_trans conf c) (q1,N1) (q2,N2) ⇒
    ffi_eq conf (c,q1,N1) (c,q2,N2)
Proof
  rw[] >>
  metis_tac[equiv_irrel_cond,active_trans_def,
            internal_strans_comm]
QED

(* -- -- Equivalence Preservation *)
Theorem internal_trans_equiv_pres:
  ∀conf cA q1A N1A q2A N2A cB q1B N1B q2B N2B.
    ffi_wf (cA,q1A,N1A) ∧
    ffi_wf (cB,q1B,N1B) ∧
    ffi_eq conf (cA,q1A,N1A) (cB,q1B,N1B)       ∧
    RTC (internal_trans conf cA) (q1A,N1A) (q2A,N2A) ∧
    RTC (internal_trans conf cB) (q1B,N1B) (q2B,N2B)   ⇒
      ffi_eq conf (cA,q2A,N2A) (cB,q2B,N2B)
Proof
  rw[] >>
  irule equiv_irrel_pres >>
  metis_tac[internal_trans_equiv_irrel]
QED

(* -- Active Bisim preservation *)
Theorem active_trans_equiv_irrel:
  ∀conf c q1 N1 q2 N2.
    ffi_wf (c,q1,N1) ∧
    RTC (active_trans conf c) (q1,N1) (q2,N2) ⇒
    ffi_eq conf (c,q1,N1) (c,q2,N2)
Proof
  rw[] >>
  metis_tac[equiv_irrel_cond,
            active_strans_comm]
QED

Theorem active_trans_equiv_pres:
  ∀conf cA q1A N1A q2A N2A cB q1B N1B q2B N2B.
    ffi_wf (cA,q1A,N1A) ∧
    ffi_wf (cB,q1B,N1B) ∧
    ffi_eq conf (cA,q1A,N1A) (cB,q1B,N1B)       ∧
    RTC (active_trans conf cA) (q1A,N1A) (q2A,N2A) ∧
    RTC (active_trans conf cB) (q1B,N1B) (q2B,N2B)   ⇒
      ffi_eq conf (cA,q2A,N2A) (cB,q2B,N2B)
Proof
  rw[] >>
  irule equiv_irrel_pres >>
  metis_tac[active_trans_equiv_irrel]
QED


(* FFI Receive/Network Send Transition *)
(* -- Send Transition Bisim preservation *)
Theorem send_trans_equiv_pres:
  ∀conf cA q1A N1A q2A N2A rp d cB q1B N1B q2B N2B.
    ffi_wf (cA,q1A,N1A) ∧
    ffi_wf (cB,q1B,N1B) ∧
    ffi_eq conf (cA,q1A,N1A) (cB,q1B,N1B)       ∧
    input_trans conf cA (q1A,N1A) (rp,d) (q2A,N2A) ∧
    input_trans conf cB (q1B,N1B) (rp,d) (q2B,N2B)   ⇒
      ffi_eq conf (cA,q2A,N2A) (cB,q2B,N2B)
Proof
  rw[] >>
  ‘∃q2Bb N2Bb.
    strans conf (cB,q1B,N1B) (ASend rp d) (cB,q2Bb,N2Bb) ∧
    ffi_eq conf (cA,q2A,N2A) (cB,q2Bb,N2Bb)’
    by (pop_assum (K ALL_TAC) >>
        ntac 2 (last_x_assum (K ALL_TAC)) >>
        ‘strans conf (cA,q1A,N1A) (ASend rp d) (cA,q2A,N2A)’
          by (irule strans_send_construct >>
              ‘q2A = q1A’
                by fs[input_trans_def] >>
              fs[] >>
              MAP_EVERY qexists_tac [‘N1A’,‘N2A’,‘q1A’] >>
              metis_tac[RTC_REFL]) >>
        qpat_x_assum ‘input_trans _ _ _ _ _’ (K ALL_TAC) >>
        last_x_assum (strip_assume_tac o
                      REWRITE_RULE [ffi_eq_def,
                                    BISIM_REL_def,
                                    BISIM_def]) >>
        fs[] >>
        rename1 ‘BR _ _’ >>
        ‘∃c3 q3 N3.
          strans conf (cB,q1B,N1B) (ASend rp d) (c3,q3,N3) ∧
          BR (cA,q2A,N2A) (c3,q3,N3)’
          by (fs[pairTheory.FORALL_PROD,
                 pairTheory.EXISTS_PROD] >>
              metis_tac[]) >>
        MAP_EVERY qexists_tac [‘q3’,‘N3’] >>
        ‘c3 = cB’
          suffices_by (rw[ffi_eq_def,BISIM_REL_def,
                          BISIM_def] >>
                       metis_tac[]) >>
        metis_tac[strans_pres_pnum,pairTheory.FST]) >>
  fs[strans_send_equiv] >>
  rename[‘RTC (active_trans conf cB) (q1B,N1B) (qIBa,NIBa)’,
         ‘input_trans conf cB (qIBa,NIBa) (rp,d) (qIBb,NIBb)’,
         ‘RTC (internal_trans conf cB) (qIBb,NIBb) (q2Bb,N2Bb)’] >>
  ‘ffi_eq conf (cB,qIBb,NIBb) (cA,q2A,N2A)’
    by (‘ffi_eq conf (cB,qIBb,NIBb) (cB,q2Bb,N2Bb)’
          suffices_by metis_tac[ffi_eq_equivRel,equivalence_def,
                                symmetric_def,transitive_def] >>
        metis_tac[active_trans_pres_wf,
                  input_trans_pres_wf,
                  internal_trans_equiv_irrel]) >>
  ‘ffi_eq conf (cB,q2B,N2B) (cB,qIBb,NIBb)’
    suffices_by metis_tac[ffi_eq_equivRel,equivalence_def,
                                symmetric_def,transitive_def] >>
  drule_all_then strip_assume_tac active_send_comm >>
  rename [‘input_trans conf cB (qIBb,NIBa) (rp,d) NS’,
          ‘input_trans conf cB (qIBb,NIBa) (rp,d) (qOS,NOS)’] >>
  ‘NS = (qOS,NOS)’
    suffices_by (rw[] >>
                 metis_tac[input_trans_pres_wf,
                           active_trans_equiv_irrel]) >>
  PairCases_on ‘NS’ >> fs[input_trans_def] >>
  irule trans_notau_functional >>
  MAP_EVERY qexists_tac [‘LReceive cB d rp’,‘NIBa’,‘conf’] >>
  rw[] >> metis_tac[ffi_wf_def,active_trans_pres_wf]
QED

(* -- Receive Transition Bisim preservation *)
Theorem receive_trans_equiv_pres:
  ∀conf cA q1A N1A q2A N2A sp d cB q1B N1B q2B N2B.
    ffi_wf (cA,q1A,N1A) ∧
    ffi_wf (cB,q1B,N1B) ∧
    ffi_eq conf (cA,q1A,N1A) (cB,q1B,N1B)       ∧
    output_trans conf cA (q1A,N1A) (sp,d) (q2A,N2A) ∧
    output_trans conf cB (q1B,N1B) (sp,d) (q2B,N2B)   ⇒
      ffi_eq conf (cA,q2A,N2A) (cB,q2B,N2B)
Proof
  rw[] >>
  ‘∃q2Bb N2Bb.
    strans conf (cB,q1B,N1B) (ARecv sp d) (cB,q2Bb,N2Bb) ∧
    ffi_eq conf (cA,q2A,N2A) (cB,q2Bb,N2Bb)’
    by (pop_assum (K ALL_TAC) >>
        ntac 2 (last_x_assum (K ALL_TAC)) >>
        ‘strans conf (cA,q1A,N1A) (ARecv sp d) (cA,q2A,N2A)’
          by (irule strans_receive_construct >>
              ‘N1A = N2A’
                by fs[output_trans_def] >>
              fs[] >>
              MAP_EVERY qexists_tac [‘N2A’,‘q1A’,‘q2A’] >>
              metis_tac[RTC_REFL]) >>
        qpat_x_assum ‘output_trans _ _ _ _ _’ (K ALL_TAC) >>
        last_x_assum (strip_assume_tac o
                      REWRITE_RULE [ffi_eq_def,
                                    BISIM_REL_def,
                                    BISIM_def]) >>
        fs[] >>
        rename1 ‘BR _ _’ >>
        ‘∃c3 q3 N3.
          strans conf (cB,q1B,N1B) (ARecv sp d) (c3,q3,N3) ∧
          BR (cA,q2A,N2A) (c3,q3,N3)’
          by (fs[pairTheory.FORALL_PROD,
                 pairTheory.EXISTS_PROD] >>
              metis_tac[]) >>
        MAP_EVERY qexists_tac [‘q3’,‘N3’] >>
        ‘c3 = cB’
          suffices_by (rw[ffi_eq_def,BISIM_REL_def,
                          BISIM_def] >>
                       metis_tac[]) >>
        metis_tac[strans_pres_pnum,pairTheory.FST]) >>
  fs[strans_receive_equiv] >>
  rename[‘RTC (active_trans conf cB) (q1B,N1B) (qIBa,NIB)’,
         ‘output_trans conf cB (qIBa,NIB) (rp,d) (qIBb,NIB)’,
         ‘RTC (internal_trans conf cB) (qIBb,NIB) (q2Bb,N2Bb)’] >>
  ‘ffi_eq conf (cB,qIBb,NIB) (cA,q2A,N2A)’
    by (‘ffi_eq conf (cB,qIBb,NIB) (cB,q2Bb,N2Bb)’
          suffices_by metis_tac[ffi_eq_equivRel,equivalence_def,
                                symmetric_def,transitive_def] >>
        metis_tac[active_trans_pres_wf,
                  output_trans_pres_wf,
                  internal_trans_equiv_irrel]) >>
  ‘ffi_eq conf (cB,q2B,N2B) (cB,qIBb,NIB)’
    suffices_by metis_tac[ffi_eq_equivRel,equivalence_def,
                                symmetric_def,transitive_def] >>
  drule_all_then strip_assume_tac active_rec_comm >>
  rename [‘output_trans conf cB (qIBa,NIB) (rp,d) NS’,
          ‘output_trans conf cB (qIBa,NIB) (rp,d) (qOS,NOS)’] >>
  PairCases_on ‘NS’ >>
  ‘qsame NS0 qOS ∧ NS1 = NOS’
    suffices_by (rw[] >>
                 ‘ffi_eq conf (cB,q2B,N2B) (cB,NS0,NOS)’
                  suffices_by metis_tac[qsame_irrel_ffi_eq,
                                        ffi_eq_equivRel,
                                        equivalence_def,
                                        transitive_def] >>
                 metis_tac[output_trans_pres_wf,
                           active_trans_equiv_irrel]) >>
  fs[qsame_def,output_trans_def] >>
  qpat_x_assum ‘NS0 = NS0 |+ _’ mp_tac >>
  qpat_x_assum ‘qOS = qOS |+ _’ mp_tac >>
  qpat_x_assum ‘NS0 |+ _ = qOS |+ _’ mp_tac >>
  rpt (pop_assum (K ALL_TAC)) >>
  fs[qlk_def,fget_def] >>
  rw[] >>
  reverse (Cases_on ‘sp = rp’)
  >- metis_tac[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on ‘FLOOKUP NS0 rp’ >>
  Cases_on ‘FLOOKUP qOS rp’ >>
  fs[finite_mapTheory.FLOOKUP_EXT,
     FUN_EQ_THM] >>
  last_x_assum (qspec_then ‘rp’ assume_tac) >>
  fs[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* EQUIVALENCE PRESERVATION *)
Theorem ffi_eq_pres:
  ∀conf SA1 SA2 L SB1 SB2.
    ffi_wf SA1 ∧
    ffi_wf SA2 ∧
    ffi_eq conf SA1 SA2   ∧
    strans conf SA1 L SB1 ∧
    strans conf SA2 L SB2   ⇒
    ffi_eq conf SB1 SB2
Proof
  rw[] >>
  MAP_EVERY PairCases_on [‘SA1’,‘SA2’,‘SB1’,‘SB2’] >>
  ‘SB10 = SA10 ∧ SB20 = SA20’
    by metis_tac[pairTheory.FST,strans_pres_pnum] >>
  Cases_on ‘L’ >>
  fs[strans_send_equiv,strans_receive_equiv,pairTheory.FST] >>
  metis_tac[active_trans_equiv_pres,
            active_trans_pres_wf,
            send_trans_equiv_pres,
            input_trans_pres_wf,
            receive_trans_equiv_pres,
            output_trans_pres_wf,
            internal_trans_equiv_pres,
            internal_trans_pres_wf]
QED

val _ = export_theory ();