open HolKernel boolLib Parse bossLib;
open pairTheory
     pred_setTheory
     relationTheory
     listTheory
     rich_listTheory;
open payloadSemTheory
     payloadLangTheory
     comms_ffi_modelTheory
     comms_ffi_consTheory;

val _ = new_theory "comms_ffi_ARecv_wf";

Definition non_empty_queues_def:
  non_empty_queues (qs : proc |-> datum list) =
    SET_TO_LIST (FDOM (normalise_queues qs))
End

Definition queue_length_def:
  queue_length (qs : proc |-> datum list) (sp : proc) =
    LENGTH (qlk qs sp)
End

Definition total_queues_data:
  total_queues_data (qs : proc |-> datum list) =
    FOLDL $+ 0 (MAP (queue_length qs) (non_empty_queues qs))
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
  (endpoint_await_send (st : state) (Send _ vn n _)   =
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
  (endpoint_await_receive (st : state) (Receive p _ _ _)   =
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



Definition total_state_info_def:
  total_state_info ((_,q,N) : total_state) =
    (net_size N, net_await_send N, total_queues_data q)
End

(* Total State Relation *)
Definition TSR_def:
  TSR (x : total_state) (y : total_state) ⇔
    ($< LEX ($< LEX $<)) (total_state_info x) (total_state_info y)
End

Theorem WF_TSR:
  WF TSR
Proof
  ‘WF (($< : num -> num -> bool) LEX (($< : num -> num -> bool) LEX ($< : num -> num -> bool)))’
    by (irule WF_LEX >> rw[] >>
        irule WF_LEX >> rw[]) >>
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

(*
Theorem LTau_net_props:
  ∀conf N1 N2.
    conf.payload_size > 0 ∧
    trans conf N1 LTau N2 ⇒
    (net_size N1 > net_size N2) ∨
    (net_size N1 = net_size N2 ∧
     net_await_send N1 > net_await_send N2)
Proof
  Induct_on ‘trans’ >>
  rw[]
  rw[net_size_def,net_await_send_def,endpoint_size_def,
     endpoint_await_send_def]
  >- (drule_all_then strip_assume_tac LReceive_net_props >>
      drule_all_then strip_assume_tac LSend_net_props >>
      rw[])
  >- (drule_all_then strip_assume_tac LReceive_net_props >>
      drule_all_then strip_assume_tac LSend_net_props >>
      rw[])
  Cases_on ‘net_size N1 > net_size N2’ >> rw[]
QED

*)

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


Theorem WF_ARecv:
  ∀conf.
    conf.payload_size > 0 ⇒
    WF (λs1 s2. ∃sp d. strans conf s2.ffi_state (ARecv sp d) s1.ffi_state)
Proof
  cheat
QED

val _ = export_theory ();
