open HolKernel boolLib Parse bossLib;
open optionTheory
     relationTheory;
open ffiTheory;
open confluenceTheory
     payloadPropsTheory
     payloadSemanticsTheory
     payloadLangTheory
     comms_ffi_modelTheory
     comms_ffi_propsTheory
     comms_ffi_consTheory;

val _ = new_theory "comms_ffi_comm";

(* INTER-PIECE COMMUTATIVITY *)
(* Internal Commutativity *)
(* -- internal/active *)
Theorem internal_active_comm:
  ∀conf c S1 S2A S2B.
    ffi_wf (c,S1) ∧
    RTC (internal_trans conf c) S1 S2A ∧
    RTC (active_trans conf c) S1 S2B ⇒
    ∃S3.
      RTC (active_trans conf c) S2A S3 ∧
      RTC (internal_trans conf c) S2B S3
Proof
  rw[] >>
  irule rc_diam_to_rtc_diam >> 
  MAP_EVERY qexists_tac [‘S1’,‘(λx. ffi_wf (c,x))’] >>
  rw[]
  >- (rename [‘_ _ _ S1f S2Af’,‘_ _ _ S1f S2Bf’,
              ‘RC _ S2Af _ ∧ RC _ S2Bf _’] >>
      rpt (qpat_x_assum ‘RTC _ _ _’ (K ALL_TAC)) >>
      MAP_EVERY PairCases_on [‘S1f’,‘S2Af’,‘S2Bf’] >>
      ‘∀ i j k l.
        RC (internal_trans conf c) (i,j) (k,l) =
          (i = k ∧ RC (λn1 n2. trans conf n1 LTau n2) j l)’
        by (fs[RC_DEF,internal_trans_def] >> metis_tac[]) >>
      ‘∀ i j k l.
        RC (emit_trans conf c) (i,j) (k,l) =
          ((i = k ∧ j = l) ∨
           (∃sp d.
              k = qpush i sp d ∧
              (λn1 n2. trans conf n1 (LSend sp d c) n2) j l))’
        by (fs[RC_DEF,emit_trans_def] >> metis_tac[]) >>
      fs[active_trans_def]
      >- (‘∃S3.
            RC (internal_trans conf c) (S2Af0,S2Af1) S3 ∧
            RC (internal_trans conf c) (S2Bf0,S2Bf1) S3’
            suffices_by (rw[] >> qexists_tac ‘S3’ >>
                         pop_assum (assume_tac o
                                    REWRITE_RULE [RC_DEF]) >>
                         PairCases_on ‘S3’ >>
                         fs[RC_DEF,active_trans_def]) >>
          fs[internal_trans_def,pairTheory.EXISTS_PROD] >>
          irule trans_diamond >> rw[compat_labels_def] >>
          qexists_tac ‘S1f1’ >> fs[wf_label_def,ffi_wf_def])
      >- (‘∃S3.
            RC (emit_trans conf c) (S2Af0,S2Af1) S3 ∧
            RC (internal_trans conf c) (S2Bf0,S2Bf1) S3’
            suffices_by (rw[] >> qexists_tac ‘S3’ >>
                         pop_assum (assume_tac o
                                    REWRITE_RULE [RC_DEF]) >>
                         PairCases_on ‘S3’ >>
                         fs[RC_DEF,active_trans_def]) >>
          fs[internal_trans_def,emit_trans_def,pairTheory.EXISTS_PROD] >>
          qspecl_then [‘S1f1’,‘LTau’,‘S2Af1’,
                       ‘LSend sp d c’,‘S2Bf1’]
                      assume_tac trans_diff_diamond >>
          rfs[ffi_wf_def,compat_labels_def,wf_label_def] >>
          rename [‘trans conf S2Bf1 LTau N3’,
                  ‘trans conf S2Af1 (LSend sp d c) N3’] >>
          qexists_tac ‘N3’ >> rw[RC_DEF] >>
          metis_tac[]))
  >- (rename [‘ffi_wf (c,ks)’,‘internal_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,internal_trans_def])
  >- (rename [‘ffi_wf (c,ks)’,‘active_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,active_trans_def,
                internal_trans_def,emit_trans_def])
QED

(* -- internal/send *)
Theorem internal_send_comm:
  ∀conf c S1 S2A S2B ML.
    ffi_wf (c,S1) ∧
    RTC (internal_trans conf c) S1 S2A ∧
    input_trans conf c S1 ML S2B ⇒
    ∃S3.
      input_trans conf c S2A ML S3 ∧
      RTC (internal_trans conf c) S2B S3
Proof
  rw[] >>
  qspecl_then [‘internal_trans conf c’,
               ‘(λn1 n2. input_trans conf c n1 ML n2)’,
               ‘(λx. ffi_wf (c,x))’]
              assume_tac
              diam_to_srtc_diam >> 
  qmatch_asmsub_abbrev_tac ‘A ⇒ B’ >>
  ‘A’
    suffices_by (rw[] >> fs[] >>
                 qunabbrev_tac ‘B’ >>
                 pop_assum (K ALL_TAC) >>
                 first_x_assum irule >>
                 metis_tac[]) >>
  ntac 4 (last_x_assum (K ALL_TAC)) >>
  MAP_EVERY qunabbrev_tac [‘A’,‘B’] >>
  rw[]
  >- (rename [‘ffi_wf (c,ks)’,‘internal_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,internal_trans_def])
  >- (rename [‘ffi_wf (c,ks)’,‘input_trans conf c ks ML us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘ML’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,input_trans_def])
  >- (MAP_EVERY PairCases_on [‘S1’,‘S2A’,‘ML’,‘S2B’] >>
      fs[input_trans_def,internal_trans_def,
         pairTheory.EXISTS_PROD] >>
      irule trans_diff_diamond >>
      fs[ffi_wf_def,compat_labels_def,wf_label_def] >>
      metis_tac[])
QED

(* -- internal/receive *)
Theorem internal_rec_comm:
  ∀conf c S1 S2A S2B ML.
    ffi_wf (c,S1) ∧
    RTC (internal_trans conf c) S1 S2A ∧
    output_trans conf c S1 ML S2B ⇒
    ∃S3.
      output_trans conf c S2A ML S3 ∧
      RTC (internal_trans conf c) S2B S3
Proof
  rw[pairTheory.EXISTS_PROD] >>
  MAP_EVERY PairCases_on [‘S1’,‘S2A’,‘S2B’,‘ML’] >>
  ‘S2A0 = S10’
    by (qpat_x_assum ‘RTC _ _ _’ mp_tac >>
        MAP_EVERY qid_spec_tac [‘S10’,‘S11’,‘S2A0’,‘S2A1’] >>
        Induct_on ‘RTC’ >> rw[] >> rename1 ‘RTC _ SI _’ >>
        PairCases_on ‘SI’ >> fs[internal_trans_def]) >>
  ‘S2B1 = S11’
    by fs[output_trans_def] >>
  fs[] >>
  MAP_EVERY qexists_tac [‘S2B0’,‘S2A1’] >>
  rw[] >- fs[output_trans_def] >>
  last_x_assum (K ALL_TAC) >>
  pop_assum (K ALL_TAC) >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘S10’,‘S11’,‘S2B0’,‘S2A1’] >>
  Induct_on ‘RTC’ >> rw[]
  >- metis_tac[RTC_REFL] >>
  rename1 ‘RTC _ SI (S10,S2A1)’ >>
  PairCases_on ‘SI’ >>
  ‘S10 = SI0’
    by fs[internal_trans_def] >>
  fs[] >> 
  ‘internal_trans conf c (S2B0,S11) (S2B0,SI1)’
    suffices_by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SINGLE] >>
  fs[internal_trans_def]
QED

(* -- internal/internal *)
Theorem internal_internal_comm:
  ∀conf c S1 S2A S2B.
    ffi_wf (c,S1) ∧
    RTC (internal_trans conf c) S1 S2A ∧
    RTC (internal_trans conf c) S1 S2B ⇒
    ∃S3.
      RTC (internal_trans conf c) S2A S3 ∧
      RTC (internal_trans conf c) S2B S3
Proof
  rw[] >>
  irule rc_diam_to_rtc_diam >> 
  MAP_EVERY qexists_tac [‘S1’,‘(λx. ffi_wf (c,x))’] >>
  rw[]
  >- (rename [‘_ _ _ S1f S2Af’,‘_ _ _ S1f S2Bf’,
              ‘RC _ S2Af _ ∧ RC _ S2Bf _’] >>
      rpt (qpat_x_assum ‘RTC _ _ _’ (K ALL_TAC)) >>
      MAP_EVERY PairCases_on [‘S1f’,‘S2Af’,‘S2Bf’] >>
      ‘∀ i j k l.
        RC (internal_trans conf c) (i,j) (k,l) =
          (i = k ∧ RC (λn1 n2. trans conf n1 LTau n2) j l)’
        by (fs[RC_DEF,internal_trans_def] >> metis_tac[]) >>
      fs[internal_trans_def,pairTheory.EXISTS_PROD] >>
      irule trans_diamond >> rw[compat_labels_def] >>
      qexists_tac ‘S1f1’ >>
      fs[wf_label_def,ffi_wf_def])
  >- (rename [‘ffi_wf (c,ks)’,‘internal_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,internal_trans_def])
  >- (rename [‘ffi_wf (c,ks)’,‘internal_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,internal_trans_def])
QED

(* Active Commutativity *)
(* -- active/active *)
Theorem active_active_comm:
  ∀conf c S1 S2A S2B.
    ffi_wf (c,S1) ∧
    RTC (active_trans conf c) S1 S2A ∧
    RTC (active_trans conf c) S1 S2B ⇒
    ∃S3.
      RTC (active_trans conf c) S2A S3 ∧
      RTC (active_trans conf c) S2B S3
Proof
  rw[] >>
  irule rc_diam_to_rtc_diam >> 
  MAP_EVERY qexists_tac [‘S1’,‘(λx. ffi_wf (c,x))’] >>
  rw[]
  >- (rename [‘_ _ _ S1f S2Af’,‘_ _ _ S1f S2Bf’,
              ‘RC _ S2Af _ ∧ RC _ S2Bf _’] >>
      rpt (qpat_x_assum ‘RTC _ _ _’ (K ALL_TAC)) >>
      MAP_EVERY PairCases_on [‘S1f’,‘S2Af’,‘S2Bf’] >>
      ‘∀ i j k l.
        RC (internal_trans conf c) (i,j) (k,l) =
          (i = k ∧ RC (λn1 n2. trans conf n1 LTau n2) j l)’
        by (fs[RC_DEF,internal_trans_def] >> metis_tac[]) >>
      ‘∀ i j k l.
        RC (emit_trans conf c) (i,j) (k,l) =
          ((i = k ∧ j = l) ∨
           (∃sp d.
              k = qpush i sp d ∧
              (λn1 n2. trans conf n1 (LSend sp d c) n2) j l))’
        by (fs[RC_DEF,emit_trans_def] >> metis_tac[]) >>
      fs[active_trans_def]
      >- (‘∃S3.
            RC (internal_trans conf c) (S2Af0,S2Af1) S3 ∧
            RC (internal_trans conf c) (S2Bf0,S2Bf1) S3’
            suffices_by (rw[] >> qexists_tac ‘S3’ >>
                         pop_assum (assume_tac o
                                    REWRITE_RULE [RC_DEF]) >>
                         PairCases_on ‘S3’ >>
                         fs[RC_DEF,active_trans_def]) >>
          fs[internal_trans_def,pairTheory.EXISTS_PROD] >>
          irule trans_diamond >> rw[compat_labels_def] >>
          qexists_tac ‘S1f1’ >> fs[wf_label_def,ffi_wf_def])
      >- (‘∃S3.
            RC (emit_trans conf c) (S2Af0,S2Af1) S3 ∧
            RC (internal_trans conf c) (S2Bf0,S2Bf1) S3’
            suffices_by (rw[] >> qexists_tac ‘S3’ >>
                         pop_assum (assume_tac o
                                    REWRITE_RULE [RC_DEF]) >>
                         PairCases_on ‘S3’ >>
                         fs[RC_DEF,active_trans_def]) >>
          fs[internal_trans_def,emit_trans_def,pairTheory.EXISTS_PROD] >>
          qspecl_then [‘S1f1’,‘LTau’,‘S2Af1’,
                       ‘LSend sp d c’,‘S2Bf1’]
                      assume_tac trans_diff_diamond >>
          rfs[ffi_wf_def,compat_labels_def,wf_label_def] >>
          rename [‘trans conf S2Bf1 LTau N3’,
                  ‘trans conf S2Af1 (LSend sp d c) N3’] >>
          qexists_tac ‘N3’ >> rw[RC_DEF] >>
          metis_tac[])
    >- (‘∃S3.
          RC (internal_trans conf c) (S2Af0,S2Af1) S3 ∧
          RC (emit_trans conf c) (S2Bf0,S2Bf1) S3’
          suffices_by (rw[] >> qexists_tac ‘S3’ >>
                       pop_assum (assume_tac o
                                  REWRITE_RULE [RC_DEF]) >>
                       PairCases_on ‘S3’ >>
                       fs[RC_DEF,active_trans_def]) >>
        fs[internal_trans_def,emit_trans_def,pairTheory.EXISTS_PROD] >>
        qspecl_then [‘S1f1’,‘LSend sp d c’,‘S2Af1’,
                     ‘LTau’,‘S2Bf1’]
                    assume_tac trans_diff_diamond >>
        rfs[ffi_wf_def,compat_labels_def,wf_label_def] >>
        rename [‘trans conf S2Bf1 (LSend sp d c) N3’,
                ‘trans conf S2Af1 LTau N3’] >>
        qexists_tac ‘N3’ >> rw[RC_DEF] >>
        metis_tac[])
    >- (‘∃S3.
          RC (emit_trans conf c) (S2Af0,S2Af1) S3 ∧
          RC (emit_trans conf c) (S2Bf0,S2Bf1) S3’
          suffices_by (rw[] >> qexists_tac ‘S3’ >>
                       pop_assum (assume_tac o
                                  REWRITE_RULE [RC_DEF]) >>
                       PairCases_on ‘S3’ >>
                       fs[RC_DEF,active_trans_def]) >>
        fs[emit_trans_def,pairTheory.EXISTS_PROD] >>
        rename1 ‘trans conf S1f1 (LSend spA dA c) S2Af1’ >>
        rename1 ‘trans conf S1f1 (LSend spB dB c) S2Bf1’ >>
        Cases_on ‘spA = spB’
        >- (‘dA = dB’
              by (‘compat_labels (LReceive spA dA c) (LReceive spB dB c)’
                    suffices_by rw[compat_labels_def] >>
                  metis_tac[ffi_wf_def,send_gen_compat]) >>
            fs[] >>
            ‘S2Af1 = S2Bf1’
              by (irule trans_notau_functional >>
                  MAP_EVERY qexists_tac [‘LSend spB dB c’,‘S1f1’,‘conf’] >>
                  fs[ffi_wf_def]) >>
            MAP_EVERY qexists_tac [‘qpush S1f0 spB dB’,‘S2Af1’] >>
            rw[])
        >- (qspecl_then [‘S1f1’,‘LSend spA dA c’,‘S2Af1’,
                         ‘LSend spB dB c’,‘S2Bf1’]
                        assume_tac trans_diff_diamond >>
            rfs[ffi_wf_def,compat_labels_def,wf_label_def] >>
            rename [‘trans conf S2Bf1 (LSend spA dA c) N3’,
                    ‘trans conf S2Af1 (LSend spB dB c) N3’] >>
            MAP_EVERY qexists_tac
                      [‘qpush (qpush S1f0 spA dA) spB dB’,
                       ‘N3’] >> rw[] >>
            metis_tac[qpush_commutes])))
  >- (rename [‘ffi_wf (c,ks)’,‘active_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,active_trans_def,
                internal_trans_def,emit_trans_def])
  >- (rename [‘ffi_wf (c,ks)’,‘active_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,active_trans_def,
                internal_trans_def,emit_trans_def])
QED
(* -- active/send *)
Theorem active_send_comm:
  ∀conf c S1 S2A S2B ML.
    ffi_wf (c,S1) ∧
    RTC (active_trans conf c) S1 S2A ∧
    input_trans conf c S1 ML S2B ⇒
    ∃S3.
      input_trans conf c S2A ML S3 ∧
      RTC (active_trans conf c) S2B S3
Proof
  rw[] >>
  qspecl_then [‘active_trans conf c’,
               ‘(λn1 n2. input_trans conf c n1 ML n2)’,
               ‘(λx. ffi_wf (c,x))’]
              assume_tac
              diam_to_srtc_diam >> 
  qmatch_asmsub_abbrev_tac ‘A ⇒ B’ >>
  ‘A’
    suffices_by (rw[] >> fs[] >>
                 qunabbrev_tac ‘B’ >>
                 pop_assum (K ALL_TAC) >>
                 first_x_assum irule >>
                 metis_tac[]) >>
  ntac 4 (last_x_assum (K ALL_TAC)) >>
  MAP_EVERY qunabbrev_tac [‘A’,‘B’] >>
  rw[]
  >- (rename [‘ffi_wf (c,ks)’,‘active_trans conf c ks us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,active_trans_def,
                internal_trans_def,emit_trans_def])
  >- (rename [‘ffi_wf (c,ks)’,‘input_trans conf c ks ML us’] >>
      MAP_EVERY PairCases_on [‘ks’,‘ML’,‘us’] >>
      metis_tac[trans_pres_wf,trans_pres_nodes,
                ffi_wf_def,input_trans_def])
  >- (MAP_EVERY PairCases_on [‘S1’,‘S2A’,‘ML’,‘S2B’] >>
      fs[pairTheory.EXISTS_PROD,active_trans_def]
      >- (‘∃N30 N31.
            input_trans conf c (S2A0,S2A1) (ML0,ML1) (N30,N31) ∧
            internal_trans conf c (S2B0,S2B1) (N30,N31)’
            suffices_by metis_tac[] >>
          fs[input_trans_def,internal_trans_def] >>
          irule trans_diff_diamond >>
          fs[ffi_wf_def,compat_labels_def,wf_label_def] >>
          metis_tac[])
      >- (‘∃N30 N31.
            input_trans conf c (S2A0,S2A1) (ML0,ML1) (N30,N31) ∧
            emit_trans conf c (S2B0,S2B1) (N30,N31)’
            suffices_by metis_tac[] >>
          fs[input_trans_def,emit_trans_def] >>
          rename1 ‘trans conf S11 (LSend sp dA c) S2A1’ >>
          rename1 ‘trans conf S11 (LReceive c dB rp) S2B1’ >>
          qspecl_then [‘S11’,‘LSend sp dA c’,‘S2A1’,
                       ‘LReceive c dB rp’,‘S2B1’]
                      assume_tac trans_diff_diamond >>
          rfs[ffi_wf_def,wf_label_def,compat_labels_def] >>
          qexists_tac ‘N3’ >> rw[] >> metis_tac[]))
QED

(* -- active/receive *)
Theorem active_rec_comm:
  ∀conf c S1 S2A S2B ML.
    ffi_wf (c,S1) ∧
    RTC (active_trans conf c) S1 S2A ∧
    output_trans conf c S1 ML S2B ⇒
    ∃S3.
      output_trans conf c S2A ML S3 ∧
      RTC (active_trans conf c) S2B S3
Proof
  rw[pairTheory.EXISTS_PROD] >>
  MAP_EVERY PairCases_on [‘S1’,‘S2A’,‘S2B’,‘ML’] >>
  ‘S2B1 = S11’
    by fs[output_trans_def] >>
  fs[] >>
  pop_assum (K ALL_TAC) >>
  ntac 2 (pop_assum mp_tac) >>
  pop_assum (K ALL_TAC) >>
  MAP_EVERY qid_spec_tac [‘S10’,‘S11’,‘S2B0’,‘S2A1’] >>
  Induct_on ‘RTC’ >> rw[]
  >- metis_tac[RTC_REFL] >>
  rename1 ‘RTC _ SI (S2A0,S2A1)’ >>
  PairCases_on ‘SI’ >>
  pop_assum (qspecl_then [‘SI1’,‘SI0’] assume_tac) >>
  fs[] >>
  ‘∃SG0 SG1.
    output_trans conf c (SI0,SI1) (ML0,ML1) (SG0,SG1) ∧
    active_trans conf c (S2B0,S11) (SG0,SG1)’
    suffices_by (rw[] >>
                 ‘SG1 = SI1’
                   by fs[output_trans_def] >>
                 fs[] >> last_x_assum (drule_all_then strip_assume_tac) >>
                 metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SINGLE]) >>
  pop_assum (K ALL_TAC) >>
  qpat_x_assum ‘RTC _ _ _’ (K ALL_TAC) >>
  last_x_assum (assume_tac o REWRITE_RULE [active_trans_def]) >>
  fs[]
  >- (‘∃SG0 SG1.
        output_trans conf c (SI0,SI1) (ML0,ML1) (SG0,SG1) ∧
        internal_trans conf c (S2B0,S11) (SG0,SG1)’
        suffices_by metis_tac[active_trans_def] >>
      fs[output_trans_def,internal_trans_def])
  >- (‘∃SG0 SG1.
        output_trans conf c (SI0,SI1) (ML0,ML1) (SG0,SG1) ∧
        emit_trans conf c (S2B0,S11) (SG0,SG1)’
        suffices_by metis_tac[active_trans_def] >>
      fs[output_trans_def,emit_trans_def] >>
      qexists_tac ‘qpush S2B0 sp d’ >> rw[]
      >- (rw[qpush_def] >>
          Cases_on ‘ML0 = sp’
          >- (rw[qlk_def,fget_def] >>
              Cases_on ‘FLOOKUP S2B0 ML0’ >>
              simp[finite_mapTheory.FLOOKUP_UPDATE])
          >- (rw[qlk_def,fget_def] >> 
              MAP_EVERY Cases_on [‘FLOOKUP S2B0 ML0’,‘FLOOKUP S2B0 sp’] >>
              simp[finite_mapTheory.FLOOKUP_UPDATE,
                   finite_mapTheory.FUPDATE_COMMUTES]))
      >- (rw[qpush_def] >>
          Cases_on ‘ML0 = sp’
          >- (rw[qlk_def,fget_def] >>
              Cases_on ‘FLOOKUP S2B0 ML0’ >>
              simp[finite_mapTheory.FLOOKUP_UPDATE])
          >- (fs[qlk_def,fget_def] >> 
              MAP_EVERY Cases_on [‘FLOOKUP S2B0 ML0’,‘FLOOKUP S2B0 sp’] >>
              fs[finite_mapTheory.FLOOKUP_UPDATE,
                 finite_mapTheory.FUPDATE_COMMUTES] >>
              metis_tac[]))
      >- metis_tac[])
QED

(* -- active/internal *)
Theorem active_internal_comm:
  ∀conf c S1 S2A S2B.
    ffi_wf (c,S1) ∧
    RTC (active_trans conf c) S1 S2A ∧
    RTC (internal_trans conf c) S1 S2B ⇒
    ∃S3.
      RTC (internal_trans conf c) S2A S3 ∧
      RTC (active_trans conf c) S2B S3
Proof
  metis_tac[internal_active_comm]
QED

(* STRANS COMMUTATIVITY *)
(* General Theorem on Conditions *)
Theorem strans_comm_cond:
  ∀ts.
    (* ASSUMPTIONS *)
    (* 1. ts preserves well formedness *)
    (∀conf c q1 N1 q2 N2.
      RTC (ts conf c) (q1,N1) (q2,N2) ⇒
      ffi_wf (c,q1,N1) ⇒
      ffi_wf (c,q2,N2)) ∧
    (* 2. Commutes with active_trans *)
    (∀conf c q1 N1 q2A N2A q2B N2B.
      ffi_wf (c,q1,N1) ∧
      RTC (ts conf c)           (q1,N1) (q2A,N2A) ∧
      RTC (active_trans conf c) (q1,N1) (q2B,N2B) ⇒
      ∃q3 N3.
        RTC (active_trans conf c) (q2A,N2A) (q3,N3) ∧
        RTC (ts conf c)           (q2B,N2B) (q3,N3)) ∧
    (* 3. Commutes with input_trans *)
    (∀conf c q1 N1 q2A N2A q2B N2B rp d.
      ffi_wf (c,q1,N1) ∧
      RTC (ts conf c) (q1,N1) (q2A,N2A) ∧
      input_trans conf c (q1,N1) (rp,d) (q2B,N2B) ⇒
      ∃q3 N3.
        input_trans conf c (q2A,N2A) (rp,d) (q3,N3) ∧
        RTC (ts conf c) (q2B,N2B) (q3,N3)) ∧
    (* 4. Commutes with output_trans *)
    (∀conf c q1 N1 q2A N2A q2B N2B sp d.
      ffi_wf (c,q1,N1) ∧
      RTC (ts conf c) (q1,N1) (q2A,N2A) ∧
      output_trans conf c (q1,N1) (sp,d) (q2B,N2B) ⇒
      ∃q3 N3.
        output_trans conf c (q2A,N2A) (sp,d) (q3,N3) ∧
        RTC (ts conf c) (q2B,N2B) (q3,N3)) ∧
    (* 5. Commutes with internal_trans *)
    (∀conf c q1 N1 q2A N2A q2B N2B.
      ffi_wf (c,q1,N1) ∧
      RTC (ts conf c)           (q1,N1) (q2A,N2A) ∧
      RTC (internal_trans conf c) (q1,N1) (q2B,N2B) ⇒
      ∃q3 N3.
        RTC (internal_trans conf c) (q2A,N2A) (q3,N3) ∧
        RTC (ts conf c)           (q2B,N2B) (q3,N3)) ⇒
    (* CONCLUSION *)
    (* Commutes with strans *)
    (∀conf c q1 N1 L q2S N2S q2T N2T.
      ffi_wf (c,q1,N1) ∧
      strans conf (c,q1,N1) L (c,q2S,N2S) ∧
      RTC (ts conf c) (q1,N1) (q2T,N2T) ⇒
      ∃q3 N3.
        RTC (ts conf c) (q2S,N2S) (q3,N3) ∧
        strans conf (c,q2T,N2T) L (c,q3,N3))
Proof
  rw[] >> Cases_on ‘L’ >>
  fs[strans_send_equiv,strans_receive_equiv]
  >- (‘ffi_wf (c,qi,ni1) ∧ ffi_wf (c,qi,ni2)
       ∧ ffi_wf (c,q2S,N2S) ∧ ffi_wf (c,q2T,N2T)’
        by metis_tac[internal_trans_pres_wf,
                     input_trans_pres_wf,
                     active_trans_pres_wf] >>
      last_x_assum (K ALL_TAC) >>
      ntac 2 (last_x_assum (drule_all_then strip_assume_tac)) >>
      last_x_assum (K ALL_TAC) >>
      last_x_assum (drule_all_then strip_assume_tac) >>
      rename [‘RTC (ts conf c) (q2S,N2S) (qF,NF)’,
              ‘RTC (active_trans conf c) (q2T,N2T) (qIE,NIE)’,
              ‘input_trans conf c (qIE,NIE) _ (qIE2,NIE2)’] >>
      ‘qIE2 = qIE’
        by fs[input_trans_def] >> fs[] >>
      MAP_EVERY qexists_tac [‘qF’,‘NF’] >> rw[] >>
      MAP_EVERY qexists_tac [‘qIE’,‘NIE’,‘NIE2’] >> rw[])
  >- (‘ffi_wf (c,qi1,ni) ∧ ffi_wf (c,qi2,ni)
       ∧ ffi_wf (c,q2S,N2S) ∧ ffi_wf (c,q2T,N2T)’
        by metis_tac[internal_trans_pres_wf,
                     output_trans_pres_wf,
                     active_trans_pres_wf] >>
      last_x_assum (K ALL_TAC) >>
      last_x_assum (drule_all_then strip_assume_tac) >>
      last_x_assum (K ALL_TAC) >>
      ntac 2  (last_x_assum (drule_all_then strip_assume_tac)) >>
      rename [‘RTC (ts conf c) (q2S,N2S) (qF,NF)’,
              ‘RTC (active_trans conf c) (q2T,N2T) (qIE,NIE)’,
              ‘output_trans conf c (qIE,NIE) _ (qIE2,NIE2)’] >>
      ‘NIE2 = NIE’
        by fs[output_trans_def] >> fs[] >>
      MAP_EVERY qexists_tac [‘qF’,‘NF’] >> rw[] >>
      MAP_EVERY qexists_tac [‘qIE’,‘qIE2’,‘NIE’] >> rw[])
QED

(* Application to Specific Pieces *)
(* -- internal/strans commutativity *)
Theorem internal_strans_comm:
  ∀conf c q1 N1 L q2S N2S q2T N2T.
    ffi_wf (c,q1,N1) ∧
    strans conf (c,q1,N1) L (c,q2S,N2S) ∧
    RTC (internal_trans conf c) (q1,N1) (q2T,N2T) ⇒
    ∃q3 N3.
      RTC (internal_trans conf c) (q2S,N2S) (q3,N3) ∧
      strans conf (c,q2T,N2T) L (c,q3,N3)
Proof
  qspec_then ‘internal_trans’ assume_tac strans_comm_cond >>
  qmatch_asmsub_abbrev_tac ‘A ⇒ B’ >>
  ‘A’ suffices_by fs[] >>
  qpat_x_assum ‘A ⇒ B’ (K ALL_TAC) >>
  MAP_EVERY qunabbrev_tac [‘A’,‘B’] >>
  rw[GSYM pairTheory.FORALL_PROD,
     GSYM pairTheory.EXISTS_PROD]
  >- metis_tac[internal_trans_pres_wf]
  >- metis_tac[internal_active_comm]
  >- metis_tac[internal_send_comm]
  >- metis_tac[internal_rec_comm]
  >- metis_tac[internal_internal_comm]
QED

(* -- active/strans commutativity *)
Theorem active_strans_comm:
  ∀conf c q1 N1 L q2S N2S q2T N2T.
    ffi_wf (c,q1,N1) ∧
    strans conf (c,q1,N1) L (c,q2S,N2S) ∧
    RTC (active_trans conf c) (q1,N1) (q2T,N2T) ⇒
    ∃q3 N3.
      RTC (active_trans conf c) (q2S,N2S) (q3,N3) ∧
      strans conf (c,q2T,N2T) L (c,q3,N3)
Proof
  qspec_then ‘active_trans’ assume_tac strans_comm_cond >>
  qmatch_asmsub_abbrev_tac ‘A ⇒ B’ >>
  ‘A’ suffices_by fs[] >>
  qpat_x_assum ‘A ⇒ B’ (K ALL_TAC) >>
  MAP_EVERY qunabbrev_tac [‘A’,‘B’] >>
  rw[GSYM pairTheory.FORALL_PROD,
     GSYM pairTheory.EXISTS_PROD]
  >- metis_tac[active_trans_pres_wf]
  >- metis_tac[active_active_comm]
  >- metis_tac[active_send_comm]
  >- metis_tac[active_rec_comm]
  >- metis_tac[active_internal_comm]
QED

val _ = export_theory ();