open HolKernel boolLib Parse bossLib;
open ffiTheory;
open bisimulationTheory
     payloadSemanticsTheory
     comms_ffi_modelTheory;

val _ = new_theory "comms_ffi_tools";

val JSPEC_THEN =
  fn spTr => fn nxTc => fn spTh => 
    FIRST[qspec_then spTr nxTc spTh, Q.ISPEC_THEN spTr nxTc spTh];

fun JSPECL_THEN []            = (fn nxTc => (fn spTh => nxTc spTh))
  | JSPECL_THEN (spTr::spTrs) =
    (fn nxTc =>
      (fn spTh =>
        let
          val recFunc = (JSPECL_THEN spTrs nxTc)
        in
          JSPEC_THEN spTr recFunc spTh
        end)
    ); 

(* Invariants under network transformation *)

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
  qabbrev_tac ‘chkPrd = λa:config s0:network l:label s1:network.
                          (∀nd. net_has_node s0 nd ⇔ net_has_node s1 nd)’ >>
  ‘∀conf S1 L S2.
    trans conf S1 L S2 ⇒ chkPrd conf S1 L S2’
    suffices_by (qunabbrev_tac ‘chkPrd’ >> rw[] >>
                 first_x_assum drule >> rw[]) >>
  rw[] >>
  irule trans_ind >>
  qunabbrev_tac ‘chkPrd’ >> rw[net_has_node_def]
QED

(* Conditions under which networks can receive *)

Theorem trans_receive_cond:
  ∀conf sp N d dp.
    (sp ≠ dp ∧ net_has_node N dp) ⇔
    (∃N'. trans conf N (LReceive sp d dp) N') 
Proof
  rw[EQ_IMP_THM]
  >- (Induct_on ‘N’ >> rw[net_has_node_def]
    >- (fs[] >> qexists_tac ‘NPar N'' N'’ >> rw [trans_rules])
    >- (fs[] >> qexists_tac ‘NPar N N''’ >> rw [trans_rules])
    >- (qmatch_goalsub_rename_tac ‘NEndpoint dp ps pe’ >>
        qexists_tac ‘NEndpoint dp (ps with queue := SNOC (sp,d) ps.queue) pe’ >>
        metis_tac[trans_rules]))
  >- (qabbrev_tac ‘chkPrd = λa:config s0:network l:label s1:network.
                          ∀sp d dp. (l = LReceive sp d dp) ⇒ sp ≠ dp’ >> 
      ‘∀c s1 l s2.
        trans c s1 l s2 ⇒ chkPrd c s1 l s2’
        suffices_by (qunabbrev_tac ‘chkPrd’ >> rw[] >>
                     first_x_assum drule >> rw[]) >>
      rw[] >> irule trans_ind >> qunabbrev_tac ‘chkPrd’ >>
      rw[])
  >- (qabbrev_tac ‘chkPrd = λa:config s0:network l:label s1:network.
                          ∀sp d dp. (l = LReceive sp d dp) ⇒ net_has_node s0 dp’ >> 
      ‘∀c s1 l s2.
        trans c s1 l s2 ⇒ chkPrd c s1 l s2’
        suffices_by (qunabbrev_tac ‘chkPrd’ >> rw[] >>
                     first_x_assum drule >> rw[]) >>
      rw[] >> irule trans_ind >> qunabbrev_tac ‘chkPrd’ >>
      rw[net_has_node_def])
QED

(* Invariants under ffi state transformation *)

Definition ffi_has_node_def:
  ffi_has_node nd (P,Q,N) =
    net_has_node N nd
End

Theorem strans_pres_pnum:
  ∀conf s1 L s2.
    strans conf s1 L s2 ⇒
      FST s1 = FST s2
Proof
  rw[Once strans_cases] >>
  simp[]
QED

Theorem strans_queue_pres:
  ∀conf P Q1 N1 D M Q2 N2.
    strans conf (P,Q1,N1) (ASend D M) (P,Q2,N2) ⇒
      isPREFIX Q1 Q2
Proof
  qabbrev_tac ‘chkPrd = λa:config (pa,qa,na):total_state l (pb,qb,nb):total_state.
                        (∃ms mc. l = ARecv ms mc) ∨
                        (isPREFIX qa qb)’ >>
  ‘∀conf S1 L S2.
    strans conf S1 L S2 ⇒ chkPrd conf S1 L S2’
    suffices_by (qunabbrev_tac ‘chkPrd’ >> rw[] >>
                 first_x_assum drule >> rw[]) >>
  rw[] >>
  irule strans_ind >>
  qunabbrev_tac ‘chkPrd’ >> rw[] >>
  metis_tac[rich_listTheory.IS_PREFIX_APPEND1]
QED

Theorem strans_pres_nodes:
  ∀conf s0 l s1.
    strans conf s0 l s1 ⇒
      (∀nd. ffi_has_node nd s0 ⇔ ffi_has_node nd s1)
Proof
  qabbrev_tac ‘chkPrd = λa:config s0:total_state l:action s1:total_state.
                          (∀nd. ffi_has_node nd s0 ⇔ ffi_has_node nd s1)’ >>
  ‘∀conf S1 L S2.
    strans conf S1 L S2 ⇒ chkPrd conf S1 L S2’
    suffices_by (qunabbrev_tac ‘chkPrd’ >> rw[] >>
                 first_x_assum drule >> rw[]) >>
  rw[] >>
  irule strans_ind >>
  qunabbrev_tac ‘chkPrd’ >> rw[ffi_has_node_def] >>
  metis_tac[trans_pres_nodes]
QED

(* Notion of ffi equivalence *)
Definition ffi_eq_def:
  ffi_eq conf = BISIM_REL (strans conf)
End

Theorem ffi_eq_equivRel:
  ∀conf. equivalence (ffi_eq conf)
Proof
  rw [ffi_eq_def,BISIM_REL_IS_EQUIV_REL]
QED


(* Notions of send validity, both in terms of format and actual destination *)
Definition valid_send_dest_def:
  valid_send_dest dest ffiSt = ((FST ffiSt ≠ dest) ∧ (ffi_has_node dest ffiSt))
End

Definition valid_send_call_format_def:
  valid_send_call_format conf dest s c bytes =
    ((s = "send") ∧ (c = dest) ∧ (LENGTH bytes = SUC conf.payload_size))
End

Theorem strans_send_cond:
  ∀dest S1.
    valid_send_dest dest S1 ⇔
    (∀s c bytes.
      valid_send_call_format conf dest s c bytes ⇒
      ∃S2.
        strans conf S1 (ASend c bytes)  S2)
Proof
  rw[EQ_IMP_THM]
  >- (Cases_on ‘S1’ >> qmatch_goalsub_rename_tac ‘(P,R)’ >>
      Cases_on ‘R’  >> qmatch_goalsub_rename_tac ‘(P,Q1,N1)’ >>
      ‘∃N2. trans conf N1 (LReceive P bytes c) N2’
        suffices_by metis_tac[strans_rules] >>
      fs[valid_send_dest_def,ffi_has_node_def] >>
      ‘c = dest’
          by fs[valid_send_call_format_def] >>
      fs[] >> metis_tac[trans_receive_cond])
  >- (qabbrev_tac ‘ad = REPLICATE (SUC conf.payload_size) (ARB :word8)’ >>
      first_x_assum (JSPECL_THEN [‘"send"’,‘dest’,‘ad’] strip_assume_tac) >>
      rfs[valid_send_call_format_def] >>
      ‘LENGTH ad = SUC conf.payload_size’
        by (qunabbrev_tac ‘ad’ >> simp[rich_listTheory.LENGTH_REPLICATE]) >>
      fs[] >> first_x_assum (K ALL_TAC) >>
      qabbrev_tac ‘chkPrd = λa:config s0:total_state l:action s1:total_state.
                          ∀md mc. (l = ASend md mc) ⇒ valid_send_dest md s0’ >> 
      ‘∀c s1 l s2.
        strans c s1 l s2 ⇒ chkPrd c s1 l s2’
        suffices_by (qunabbrev_tac ‘chkPrd’ >> rw[] >>
                     first_x_assum drule >> rw[]) >>
      rw[] >> irule strans_ind >> qunabbrev_tac ‘chkPrd’ >>
      rw[valid_send_dest_def,ffi_has_node_def] >>
      metis_tac[trans_pres_nodes,trans_receive_cond])
QED


(* Modelling invariants on FFI *)
Definition ffi_accepts_rel_def:
  ffi_accepts_rel stpred pred oracle =
  ∀st s conf bytes.
    stpred st.ffi_state ∧ st.oracle = oracle ∧ pred s conf bytes ⇒
    ∃ffi. st.oracle s st.ffi_state conf bytes = Oracle_return ffi bytes ∧
          stpred ffi
End

(* Proving the major send invariant *)
Theorem send_invariant:
  ∀ conf l.
    ffi_accepts_rel (valid_send_dest l) (valid_send_call_format conf l) (comms_ffi_oracle conf)
Proof
  rw[valid_send_dest_def,ffi_accepts_rel_def,valid_send_call_format_def,
     comms_ffi_oracle_def,ffi_send_def] >>
  qmatch_goalsub_abbrev_tac ‘strans _ s _’ >>
  first_x_assum (K ALL_TAC) >>
  qpat_x_assum ‘_ = comms_ffi_oracle conf’ (K ALL_TAC) >>
  rw[]
  >- (qmatch_goalsub_abbrev_tac ‘FST (@ns. C ns ) ≠ l’ >>
      ‘(λs. FST s ≠ l) (@ns. C ns)’
        suffices_by rw[] >>
      irule SELECT_ELIM_THM >>
      rw[] >> qunabbrev_tac ‘C’
      >- metis_tac[strans_pres_pnum]
      >- (qexists_tac ‘ns’ >> fs[]))
  >- (irule SELECT_ELIM_THM >> rw[]
      >- metis_tac[strans_pres_nodes]
      >- (qexists_tac ‘ns’ >> fs[]))
  >- (rename [‘¬∃s2. strans conf s1 (ASend l bytes) s2’] >>
      ‘∃s2. strans conf s1 (ASend l bytes) s2’
        suffices_by fs[] >>
      first_x_assum (K ALL_TAC) >>
      Cases_on ‘s1’ >> rename [‘ffi_has_node _ (P,R)’] >> Cases_on ‘R’ >>
      rename [‘ffi_has_node _ (P,Q1,N1)’] >> 
      ‘∃N2. trans conf N1 (LReceive P bytes l) N2’
        suffices_by metis_tac[strans_rules] >>
      fs[ffi_has_node_def] >> metis_tac[trans_receive_cond])
QED

(*
Theorem ffi_eq_sendval:
  ∀conf fs1 fs2.
    ffi_eq conf fs1 fs2 ⇒
    (∀l. valid_send_dest l fs1 ⇔ valid_send_dest l fs2)
Proof
  rw[EQ_IMP_THM] >> JSPECL_THEN [‘conf’,‘l’] assume_tac send_invariant >>
  fs[ffi_accepts_rel_def] >> qmatch_asmsub_abbrev_tac ‘valid_send_dest l KS’ >>
  qmatch_goalsub_abbrev_tac ‘valid_send_dest l US’ >>
  qabbrev_tac ‘ad = REPLICATE (SUC conf.payload_size) (ARB :word8)’ >>
  first_x_assum (JSPECL_THEN [‘<|oracle := comms_ffi_oracle conf;
                               ffi_state := KS;
                               io_events := ARB|>’,
                              ‘"send"’,‘l’,‘ad’]
                             assume_tac) >>
  ‘LENGTH ad = SUC conf.payload_size’
    by simp[Abbr ‘ad’, rich_listTheory.LENGTH_REPLICATE] >>
  fs[valid_send_call_format_def,comms_ffi_oracle_def,ffi_send_def] >>
  rfs[] >>
  Cases_on ‘∃NKS. strans conf KS (ASend l ad) NKS’ >>
  fs[] >> qpat_x_assum ‘(@X. Y) = Z’ (K ALL_TAC) >>
  ‘∃NUS. strans conf US (ASend l ad) NUS’
    by metis_tac[ffi_eq_def,BISIM_REL_def,BISIM_REL_def] >>
  Cases_on ‘US’ >> qmatch_goalsub_rename_tac ‘(P,R)’ >>
  Cases_on ‘R’ >> qmatch_goalsub_rename_tac ‘valid_send_dest l (P,QU,NU)’ >>
  Cases_on ‘NUS’ >> rename1 ‘strans conf (P,QU,NU) (ASend L AD) (PN,R)’ >>
  Cases_on ‘R’ >> rename1 ‘strans conf (P,QU,NU) (ASend L AD) (PN,QUN,NUN)’ >>
  JSPECL_THEN [‘L’,‘(P,QU,NU)’] strip_assume_tac trans_receive_cond
QED
*)
val _ = export_theory ();