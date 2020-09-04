open HolKernel boolLib Parse bossLib;
open pairTheory
     pred_setTheory
     relationTheory
     listTheory
     finite_mapTheory;
open payloadSemTheory
     payloadLangTheory
     payloadPropsTheory
     comms_ffi_modelTheory
     comms_ffi_consTheory
     comms_ffi_propsTheory;

val _ = new_theory "comms_ffi_ARecv_wf";

(* Basic Queue/Endpoint/Network Observables *)

Definition non_empty_queues_def:
  non_empty_queues (qs : proc |-> datum list) =
    FDOM (normalise_queues qs)
End

Definition queue_length_def:
  queue_length (qs : proc |-> datum list) (sp : proc) =
    LENGTH (qlk qs sp)
End

Definition total_queues_data_def:
  total_queues_data (qs : proc |-> datum list) =
    SUM_IMAGE (queue_length qs) (non_empty_queues qs)
End

Definition endpoint_size_def:
  (endpoint_size Nil               = 0) ∧
  (endpoint_size (Send _ _ _ e)    = SUC (endpoint_size e)) ∧
  (endpoint_size (Receive _ _ _ e) = SUC (endpoint_size e)) ∧
  (endpoint_size (IfThen _ e1 e2)  = SUC (endpoint_size e1 + endpoint_size e2)) ∧
  (endpoint_size (Let _ _ _ e)     = SUC (endpoint_size e))
End

Definition net_size_def:
  (net_size NNil = 0) ∧
  (net_size (NPar n1 n2) = net_size n1 + net_size n2) ∧
  (net_size (NEndpoint _ _ e) = endpoint_size e)
End

Definition endpoint_await_send_def:
  (endpoint_await_send _  Nil               = 0) ∧
  (endpoint_await_send (st : closure state) (Send _ vn n _)   =
    case FLOOKUP st.bindings vn of
      SOME x => LENGTH x - n
    | NONE   => 0) ∧
  (endpoint_await_send _  (Receive _ _ _ _) = 0) ∧
  (endpoint_await_send _  (IfThen _ _ _)    = 0) ∧
  (endpoint_await_send _  (Let _ _ _ _)     = 0)
End

Definition endpoint_await_receive_def:
  (endpoint_await_receive _  Nil            = 0) ∧
  (endpoint_await_receive _ (Send _ _ _ _)  = 0) ∧
  (endpoint_await_receive (st : closure state) (Receive p _ _ _)   =
    queue_length st.queues p) ∧
  (endpoint_await_receive _  (IfThen _ _ _) = 0) ∧
  (endpoint_await_receive _  (Let _ _ _ _)  = 0)
End

Definition net_await_send_def:
  (net_await_send NNil = 0) ∧
  (net_await_send (NPar n1 n2) = net_await_send n1 + net_await_send n2) ∧
  (net_await_send (NEndpoint _ st e) = endpoint_await_send st e)
End

Definition net_await_receive_def:
  (net_await_receive NNil = 0) ∧
  (net_await_receive (NPar n1 n2) = net_await_receive n1 + net_await_receive n2) ∧
  (net_await_receive (NEndpoint _ st e) = endpoint_await_receive st e)
End

(* Variation in Observables over trans steps *)
Theorem LReceive_net_props:
  ∀conf N1 sp d rp N2.
    trans conf N1 (LReceive sp d rp) N2 ⇒
    ((net_size N1 = net_size N2) ∧
     (net_await_send N1 = net_await_send N2))
Proof
  Induct_on ‘trans’ >>
  rw[net_size_def,net_await_send_def] >>
  rename1 ‘endpoint_await_send st e = _’ >>
  Cases_on ‘e’ >>
  rw[endpoint_await_send_def]
QED

Theorem LSend_net_props:
  ∀conf N1 sp d rp N2.
    conf.payload_size > 0 ∧
    trans conf N1 (LSend sp d rp) N2 ⇒
    (net_size N1 > net_size N2) ∨
    (net_size N1 = net_size N2 ∧
     net_await_send N1 > net_await_send N2)
Proof
  Induct_on ‘trans’ >>
  rw[net_size_def,net_await_send_def,endpoint_size_def,
     endpoint_await_send_def] >>
  Cases_on ‘net_size N1 > net_size N2’ >> rw[]
QED

Theorem LTau_net_props:
  ∀conf N1 N2.
    conf.payload_size > 0 ∧
    trans conf N1 LTau N2 ⇒
    (net_size N1 > net_size N2) ∨
    (net_size N1 = net_size N2 ∧
     net_await_send N1 > net_await_send N2) ∨
    (net_size N1 = net_size N2 ∧
     net_await_send N1 = net_await_send N2 ∧
     net_await_receive N1 > net_await_receive N2)
Proof
  Induct_on ‘trans’ >>
  rw[net_size_def,net_await_send_def,net_await_receive_def,
     endpoint_size_def,endpoint_await_send_def,endpoint_await_receive_def,
     queue_length_def] >>
  Cases_on ‘net_size N1 > net_size N2’ >> rw[] >>
  drule_all_then strip_assume_tac LReceive_net_props >>
  drule_all_then strip_assume_tac LSend_net_props >>
  rw[]
QED

(* Taking Observables up to total_state and producing a relation*)
Definition total_state_info_def:
  total_state_info ((_,q,N) : total_state) =
    (net_size N, net_await_send N, net_await_receive N, total_queues_data q)
End

Definition TSR_def:
  TSR (x : total_state) (y : total_state) ⇔
    ($< LEX ($< LEX ($< LEX $<))) (total_state_info x) (total_state_info y)
End

Theorem transitive_TSR:
  transitive TSR
Proof
  rw[transitive_def,TSR_def,LEX_DEF] >>
  qmatch_goalsub_rename_tac ‘_ (total_state_info x) (total_state_info z)’ >>
  MAP_EVERY PairCases_on [‘x’,‘z’] >>
  fs[total_state_info_def] >>
  rename1 ‘total_state_info y’ >>
  PairCases_on ‘y’ >>
  fs[total_state_info_def]
QED

Theorem WF_TSR:
  WF TSR
Proof
  ‘WF ($LEX ($< : num -> num -> bool)
            ($LEX ($< : num -> num -> bool)
                  ($LEX ($< : num -> num -> bool)
                        ($< : num -> num -> bool)
                  )
            )
      )’
    by ntac 3 (irule WF_LEX >> rw[]) >>
  fs[WF_DEF,TSR_def] >> rw[] >>
  rename1 ‘B w’ >>
  first_x_assum (qspec_then ‘IMAGE total_state_info B’ mp_tac) >>
  impl_tac
  >- (rw[IMAGE_DEF,IN_DEF] >>
      metis_tac[]) >>
  rw[IN_DEF] >>
  qmatch_asmsub_rename_tac ‘∀b. _ b (_ x) ⇒ (∀x. b ≠ _ x ∨ ¬B x)’ >>
  qexists_tac ‘x’ >> rw[] >>
  qmatch_goalsub_rename_tac ‘¬B b’ >>
  first_x_assum (qspec_then ‘total_state_info b’ assume_tac) >>
  rfs[] >>
  first_x_assum (qspec_then ‘b’ assume_tac) >>
  rw[]
QED

(* Relation over strans level changes *)
Theorem internal_trans_TSR:
  ∀conf c q1 N1 q2 N2.
    conf.payload_size > 0 ∧
    internal_trans conf c (q1,N1) (q2,N2) ⇒
    TSR (c,q2,N2) (c,q1,N1)
Proof
  rw[internal_trans_def,TSR_def,LEX_DEF,total_state_info_def] >>
  drule_all_then assume_tac LTau_net_props>>
  rw[]
QED

Theorem emit_trans_TSR:
  ∀conf c q1 N1 q2 N2.
    conf.payload_size > 0 ∧
    emit_trans conf c (q1,N1) (q2,N2) ⇒
    TSR (c,q2,N2) (c,q1,N1)
Proof
  rw[emit_trans_def,TSR_def,LEX_DEF,total_state_info_def] >>
  drule_all_then assume_tac LSend_net_props>>
  rw[]
QED

Theorem active_trans_TSR:
  ∀conf c q1 N1 q2 N2.
    conf.payload_size > 0 ∧
    active_trans conf c (q1,N1) (q2,N2) ⇒
    TSR (c,q2,N2) (c,q1,N1)
Proof
  rw[active_trans_def] >>
  metis_tac[internal_trans_TSR,emit_trans_TSR]
QED

Theorem output_trans_TSR:
  ∀conf c q1 N1 sp d q2 N2.
    conf.payload_size > 0 ∧
    output_trans conf c (q1,N1) (sp,d) (q2,N2) ⇒
    TSR (c,q2,N2) (c,q1,N1)
Proof
  rw[output_trans_def,TSR_def,LEX_DEF,total_state_info_def,total_queues_data_def,
     non_empty_queues_def,SUM_IMAGE_THM] >>
  Cases_on ‘sp ∈ FDOM (normalise_queues q2)’ >>
  rw [SUM_IMAGE_DELETE,queue_length_def] >>
  ‘qlk (normalise_queues q1) sp = d::qlk q2 sp’
    by (qpat_x_assum ‘normalise_queues q1 = _’ SUBST1_TAC >>
        rw[]) >>
  fs[]
  >- (‘SUM_IMAGE (queue_length q2) (FDOM (normalise_queues q2)) < SUM_IMAGE (queue_length q1) (FDOM (normalise_queues q2))’
        suffices_by rw[] >>
      irule SUM_IMAGE_MONO_LESS >>
      rw[FDOM_FINITE]
      >- (rw[queue_length_def] >>
          rename1 ‘LENGTH (qlk _ x) ≤ LENGTH (qlk _ x)’ >>
          Cases_on ‘x = sp’
          >- rw[] >>
          ‘qlk (normalise_queues q1) x = qlk q2 x’
            suffices_by rw[] >>
          qpat_x_assum ‘normalise_queues q1 = _’ SUBST1_TAC >>
          rw[]) >>
      qexists_tac ‘sp’ >> rw[queue_length_def])
  >- (‘SUM_IMAGE (queue_length q2) (FDOM (normalise_queues q2)) = SUM_IMAGE (queue_length q1) (FDOM (normalise_queues q2))’
        suffices_by rw[] >>
      irule SUM_IMAGE_CONG >> rw[queue_length_def] >>
      rename1 ‘LENGTH (qlk _ x) = LENGTH (qlk _ x)’ >>
      ‘qlk (normalise_queues q1) x = qlk q2 x’
        suffices_by rw[] >>
      qpat_x_assum ‘normalise_queues q1 = _’ SUBST1_TAC >>
      ‘x ≠ sp’
        suffices_by rw[] >>
      metis_tac[])
QED

Theorem active_trans_TC_TSR:
  ∀conf c q1 N1 q2 N2.
    conf.payload_size > 0 ∧
    TC (active_trans conf c) (q1,N1) (q2,N2) ⇒
    TSR (c,q2,N2) (c,q1,N1)
Proof
  rw[] >> pop_assum mp_tac >>
  MAP_EVERY qabbrev_tac [‘s1 = (q1,N1)’,‘s2 = (q2,N2)’] >>
  ntac 2 (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘s2’,‘s1’] >>
  ho_match_mp_tac TC_INDUCT >> rw[]
  >- (MAP_EVERY PairCases_on [‘s1’,‘s2’] >>
      metis_tac[active_trans_TSR])
  >- metis_tac[transitive_TSR,transitive_def]
QED

Theorem internal_trans_TC_TSR:
  ∀conf c q1 N1 q2 N2.
    conf.payload_size > 0 ∧
    TC (internal_trans conf c) (q1,N1) (q2,N2) ⇒
    TSR (c,q2,N2) (c,q1,N1)
Proof
  rw[] >> pop_assum mp_tac >>
  MAP_EVERY qabbrev_tac [‘s1 = (q1,N1)’,‘s2 = (q2,N2)’] >>
  ntac 2 (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘s2’,‘s1’] >>
  ho_match_mp_tac TC_INDUCT >> rw[]
  >- (MAP_EVERY PairCases_on [‘s1’,‘s2’] >>
      metis_tac[internal_trans_TSR])
  >- metis_tac[transitive_TSR,transitive_def]
QED

Triviality WF_prop:
  ∀Q R.
    WF R ∧
    (∀x y.
      Q x y ⇒ R x y) ⇒
    WF Q
Proof
  rw[WF_DEF] >>
  rename1 ‘B w’ >>
  first_x_assum (qspec_then ‘B’ assume_tac) >>
  pop_assum mp_tac >> impl_tac
  >- metis_tac[] >>
  rw[] >> rename1 ‘∀b. R b min ⇒ ¬B b’ >>
  qexists_tac ‘min’ >> rw[]
QED

Theorem WF_ARecv_total_state:
  ∀conf sp.
    conf.payload_size > 0 ⇒
    WF (λs1 s2. ∃d. ¬(final d) ∧ strans conf s2 (ARecv sp d) s1)
Proof
  rw[] >>
  qmatch_goalsub_abbrev_tac ‘WF R’ >>
  ‘∀x y. (R x y ⇒ TSR x y)’
    suffices_by (rw[] >> metis_tac[WF_prop,WF_TSR]) >>
  qunabbrev_tac ‘R’ >>
  rw[] >>
  MAP_EVERY PairCases_on [‘x’,‘y’] >>
  ‘x0 = y0’
    by metis_tac[strans_pres_pnum,FST] >>
  fs[] >> rw[] >>
  drule_all_then strip_assume_tac strans_receive_deconstruct >>
  drule_all_then strip_assume_tac RTC_TC_RC >>
  qpat_x_assum ‘RTC (internal_trans _ _) _ _’ kall_tac >>
  drule_all_then strip_assume_tac RTC_TC_RC >>
  qpat_x_assum ‘RTC (active_trans _ _) _ _’ kall_tac >>
  fs[RC_DEF] >> rfs[] >> rw[] >>
  metis_tac[active_trans_TC_TSR,internal_trans_TC_TSR,
            active_trans_TSR,internal_trans_TSR,
            output_trans_TSR,transitive_TSR,
            transitive_def]
QED

Theorem WF_ARecv_ffi_state:
  ∀conf.
    conf.payload_size > 0 ⇒
    WF (λs1 s2. ∃sp d. strans conf s2.ffi_state (ARecv sp d) s1.ffi_state)
Proof
  rw[] >>
  drule_all_then assume_tac WF_ARecv_total_state >>
  fs[WF_DEF] >> rw[] >>
  rename1 ‘B w’ >>
  first_x_assum (qspec_then ‘IMAGE (λx. x.ffi_state) B’ mp_tac) >>
  impl_tac
  >- (rw[IMAGE_DEF,IN_DEF] >>
      metis_tac[]) >>
  rw[IN_DEF] >>
  qmatch_asmsub_rename_tac ‘∀s1.
                              (∃sp d. strans conf x.ffi_state (ARecv sp d) s1) ⇒
                              ∀x. s1 ≠ x.ffi_state ∨ ¬B x’ >>
  qexists_tac ‘x’ >> rw[] >>
  qmatch_goalsub_rename_tac ‘¬B b’ >>
  first_x_assum (qspec_then ‘(λx. x.ffi_state) b’ assume_tac) >>
  pop_assum mp_tac >>
  impl_tac >- metis_tac[] >>
  rw[] >>
  first_x_assum (qspec_then ‘b’ assume_tac) >>
  rw[]
QED

val _ = export_theory ();
