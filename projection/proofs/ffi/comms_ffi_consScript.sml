open HolKernel boolLib Parse bossLib;
open relationTheory;
open payloadSemanticsTheory;
open comms_ffi_modelTheory;

val _ = new_theory "comms_ffi_cons";

(* BUILDING BLOCK TRANSITIONS *)
(* Internal Transition *)
Definition internal_trans_def:
  internal_trans conf (c:proc) (q1:queues,n1:network) (q2:queues,n2:network) ⇔
    trans conf n1 LTau n2 ∧ q1 = q2
End

(* Emission Transition *)
Definition emit_trans_def:
  emit_trans conf (c:proc) (q1:queues,n1:network) (q2:queues,n2:network) ⇔
    ∃sp d .
      trans conf n1 (LSend sp d c) n2 ∧
      q2 = qpush q1 sp d
End

(* Emission or Internal Transition *)
Definition active_trans_def:
  active_trans conf c (q1,n1) (q2,n2) ⇔
    internal_trans conf c (q1,n1) (q2,n2) ∨
    emit_trans     conf c (q1,n1) (q2,n2)
End

(* Input Transition *)
Definition input_trans_def:
  input_trans conf c (q1,n1) (rp,d) (q2,n2) ⇔
    trans conf n1 (LReceive c d rp) n2 ∧
    q2 = q1
End

(* Output Transition *)
Definition output_trans_def:
  output_trans conf c (q1,n1) (sp,d) (q2,n2) ⇔
    (n1 = n2) ∧
    (q1 = q2 |+ (sp,d::(qlk q2 sp))) ∧
    (q2 = q2 |+ (sp,qlk q2 sp))
End


(* GENERAL CONSTRUCTION FACTS *)
(* Front Addition *)
Theorem strans_front_construct:
  ∀conf q1 n1 qi ni q2 n2 c L.
    RTC (active_trans conf c) (q1,n1) (qi,ni) ∧
    strans conf (c,qi,ni) L (c,q2,n2) ⇒
    strans conf (c,q1,n1) L (c,q2,n2)
Proof
  rpt gen_tac >>
  ‘∀S1 S2.
    RTC (active_trans conf c) S1 S2 ⇒
      (λ(q1,n1) (qi,ni).
        strans conf (c,qi,ni) L (c,q2,n2) ⇒
        strans conf (c,q1,n1) L (c,q2,n2)) S1 S2’
    suffices_by (disch_then (qspecl_then [‘(q1,n1)’,‘(qi,ni)’] assume_tac) >>
                 rw[] >> fs[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[]
  >- (Cases_on ‘S1’ >> rw[])
  >- (rename [‘active_trans conf c S1 S1B’] >>
      Cases_on ‘S1’ >> Cases_on ‘S1B’ >> Cases_on ‘S2’ >>
      rw[] >> fs[active_trans_def,internal_trans_def,emit_trans_def]
      >- metis_tac[strans_rules]
      >- metis_tac[strans_rules])
QED

(* Back Addition *)
Theorem strans_back_construct:
  ∀conf q1 n1 qi ni q2 n2 c L.
    strans conf (c,q1,n1) L (c,qi,ni) ∧
    RTC (internal_trans conf c) (qi,ni) (q2,n2)     ⇒
    strans conf (c,q1,n1) L (c,q2,n2)
Proof
  rpt gen_tac >>
  ‘∀S1 S2.
    RTC (internal_trans conf c) S1 S2 ⇒
      (λ(qi,ni) (q2,n2).
        strans conf (c,q1,n1) L (c,qi,ni) ⇒
        strans conf (c,q1,n1) L (c,q2,n2)) S1 S2’
    suffices_by (disch_then (qspecl_then [‘(qi,ni)’,‘(q2,n2)’] assume_tac) >>
                 rw[] >> fs[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[]
  >- (Cases_on ‘S1’ >> rw[])
  >- (rename [‘internal_trans conf c S1 S1B’] >>
      Cases_on ‘S1’ >> Cases_on ‘S1B’ >> Cases_on ‘S2’ >>
      rw[] >> fs[internal_trans_def] >>
      rfs[] >>
      ‘strans conf (c,q1,n1) L (c,q',r')’
        suffices_by rw[] >>
      metis_tac[strans_rules])
QED


(* SEND CONSTRUCTION/DECONSTRUCTION *)
(* Pulling apart a send operation *)
Theorem strans_send_deconstruct:
  ∀conf c q1 q2 n1 d rp n2.
    strans conf (c,q1,n1) (ASend rp d) (c,q2,n2) ⇒
    ∃ni1 ni2 qi.
      RTC (active_trans conf c) (q1,n1) (qi,ni1) ∧
      input_trans conf c (qi,ni1) (rp,d) (qi,ni2) ∧
      RTC (internal_trans conf c) (qi,ni2) (q2,n2)
Proof
  Induct_on ‘strans’ >> rw[]
  >- (MAP_EVERY qexists_tac [‘ni1’,‘ni2’,‘qi’] >>
      rename [‘trans conf N LTau Np’] >>
      ‘RTC (active_trans conf c) (q,N) (q,Np)’
        suffices_by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      irule RTC_SINGLE >>
      rw[active_trans_def,internal_trans_def])
  >- (MAP_EVERY qexists_tac [‘ni1’,‘ni2’,‘qi’] >>
      rename [‘trans conf N LTau Np’,
              ‘RTC _ (qi,ni2) (qf,N)’] >>
      ‘RTC (internal_trans conf c) (qf,N) (qf,Np)’
        suffices_by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      irule RTC_SINGLE >>
      rw[active_trans_def,internal_trans_def])
  >- (MAP_EVERY qexists_tac [‘ni1’,‘ni2’,‘qi’] >>
      rename [‘trans conf N (LSend _ _ _) Np’] >>
      ‘RTC (active_trans conf c) (q,N) (qpush q sp d,Np)’
        suffices_by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      irule RTC_SINGLE >>
      rw[active_trans_def,emit_trans_def] >>
      DISJ2_TAC >>
      metis_tac[])
  >- (metis_tac[RTC_RULES,input_trans_def])
QED 

(* Constructing a send operation *)
Theorem strans_send_construct:
  ∀conf q1 n1 qi ni1 c d rp ni2 q2 n2.
    RTC (active_trans conf c) (q1,n1) (qi,ni1) ∧
    input_trans conf c (qi,ni1) (rp,d) (qi,ni2) ∧
    RTC (internal_trans conf c) (qi,ni2) (q2,n2) ⇒
      strans conf (c,q1,n1) (ASend rp d) (c,q2,n2)
Proof
  metis_tac[input_trans_def, strans_rules,
            strans_front_construct,strans_back_construct]
QED 

(* Send Label Equivalence *)
Theorem strans_send_equiv:
  ∀conf q1 n1 c d rp q2 n2.
    strans conf (c,q1,n1) (ASend rp d) (c,q2,n2) ⇔
    ∃qi ni1 ni2.
      RTC (active_trans conf c) (q1,n1) (qi,ni1) ∧
      input_trans conf c (qi,ni1) (rp,d) (qi,ni2) ∧
      RTC (internal_trans conf c) (qi,ni2) (q2,n2)
Proof
  metis_tac[strans_send_deconstruct,strans_send_construct]
QED


(* RECEIVE CONSTRUCTION/DECONSTRUCTION *)
(* Pulling apart a receive operation *)
Theorem strans_receive_deconstruct:
  ∀conf c q1 q2 n1 d sp n2.
    strans conf (c,q1,n1) (ARecv sp d) (c,q2,n2) ⇒
    ∃qi1 qi2 ni.
      RTC (active_trans conf c) (q1,n1) (qi1,ni) ∧
      output_trans conf c (qi1,ni) (sp,d) (qi2,ni) ∧
      RTC (internal_trans conf c) (qi2,ni) (q2,n2)
Proof
  Induct_on ‘strans’ >> rw[]
  >- (rename1 ‘qlk q ms = mc::tl’ >>
      MAP_EVERY qexists_tac [‘q |+ (ms,mc::tl)’,‘q |+ (ms,tl)’,‘N’] >>
      rw[qlk_def,fget_def,finite_mapTheory.FLOOKUP_DEF,output_trans_def] >>
      ‘q |+ (ms,mc:: tl) = q’
        suffices_by (rw[] >> metis_tac[RC_DEF]) >>
      irule finite_mapTheory.FUPDATE_ELIM >>
      fs[qlk_def,fget_def,finite_mapTheory.FLOOKUP_DEF] >>
      Cases_on ‘ms ∈ FDOM q’ >> fs[])
  >- (rename [‘trans conf NA LTau NB’,
              ‘RTC _ (qA,NB) (qC,NCD)’,
              ‘output_trans conf c (qC,NCD) (sp,d) (qD,NCD)’,
              ‘RTC _ (qD,NCD) (qE,NE)’] >>
      MAP_EVERY qexists_tac [‘qC’,‘qD’,‘NCD’] >>
      fs[output_trans_def] >>
      ‘RTC (active_trans conf c) (qA,NA) (qA,NB)’
        suffices_by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      irule RTC_SINGLE >>
      rw[active_trans_def,internal_trans_def])
  >- (rename [‘RTC _ (qA,NA) (qB,NB)’,
              ‘output_trans conf c (qB,NB) (sp,d) (qC,NC)’,
              ‘RTC _ (qC,NC) (qDE,ND)’,
              ‘trans conf ND LTau NE’] >>
      MAP_EVERY qexists_tac [‘qB’,‘qC’,‘NC’] >>
      fs[output_trans_def] >>
      ‘RTC (internal_trans conf c) (qDE,ND) (qDE,NE)’
        suffices_by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      irule RTC_SINGLE >>
      rw[internal_trans_def])
  >- (rename [‘trans conf NA (LSend sp d c) NB’,
              ‘RTC _ (qpush qA sp d,NB) (qC,NCD)’,
              ‘output_trans conf c (qC,NCD) (sp2,d2) (qD,NCD)’,
              ‘RTC _ (qD,NCD) (qE,NE)’] >>
      MAP_EVERY qexists_tac [‘qC’,‘qD’,‘NCD’] >>
      fs[output_trans_def] >>
      ‘RTC (active_trans conf c) (qA,NA) (qpush qA sp d,NB)’
        suffices_by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      irule RTC_SINGLE >>
      rw[active_trans_def,emit_trans_def] >>
      metis_tac[])
QED 

(* Constructing a receive operation *)
Theorem strans_receive_construct:
  ∀conf c q1 q2 n1 d sp n2 qi1 qi2 ni.
    RTC (active_trans conf c) (q1,n1) (qi1,ni) ∧
    output_trans conf c (qi1,ni) (sp,d) (qi2,ni) ∧
    RTC (internal_trans conf c) (qi2,ni) (q2,n2) ⇒
  	strans conf (c,q1,n1) (ARecv sp d) (c,q2,n2)
Proof
  rw[] >>
  ‘strans conf (c,qi1,ni) (ARecv sp d) (c,qi2,ni)’
    suffices_by metis_tac[strans_front_construct,strans_back_construct] >>
  ‘(qlk qi1 sp = d::(qlk qi2 sp)) ∧
   (qi2 = qi1 |+ (sp,qlk qi2 sp))’
    by (fs[output_trans_def,qlk_def,fget_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  metis_tac[strans_rules]
QED 

(* Receive Label Equivalence *)
Theorem strans_receive_equiv:
  ∀conf c q1 q2 n1 d sp n2.
    strans conf (c,q1,n1) (ARecv sp d) (c,q2,n2) ⇔
    ∃qi1 qi2 ni.
      RTC (active_trans conf c) (q1,n1) (qi1,ni) ∧
      output_trans conf c (qi1,ni) (sp,d) (qi2,ni) ∧
      RTC (internal_trans conf c) (qi2,ni) (q2,n2)
Proof
  metis_tac[strans_receive_deconstruct,strans_receive_construct]
QED

val _ = export_theory ();