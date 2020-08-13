open preamble payloadLangTheory

val _ = new_theory "payloadSem";

Datatype:
 label = LSend proc datum proc
       | LReceive proc datum proc
       | LTau
End

Inductive trans:
  (* Send-last-payload *)
  (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n <= conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 v n e))
                 (LSend p1 (pad conf (DROP n d)) p2)
                 (NEndpoint p1 s e)) ∧

  (* Send-intermediate-payload *)
  (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n > conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 v n e))
                  (LSend p1 (pad conf (DROP n d)) p2)
                  (NEndpoint p1 s (Send p2 v (n + conf.payload_size) e))) ∧

  (* Enqueue *)
  (∀conf s d p1 p2 e.
    p1 ≠ p2
    ⇒ trans conf (NEndpoint p2 s e)
             (LReceive p1 d p2)
             (NEndpoint p2 (s with queues := qpush s.queues p1 d) e)) ∧

  (* Com-L *)
  (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LSend p1 d p2) n1'
    ∧ trans conf n2 (LReceive p1 d p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2')) ∧

  (* Com-R *)
  (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LReceive p1 d p2) n1'
    ∧ trans conf n2 (LSend p1 d p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2')) ∧

  (* Dequeue-last-payload *)
  (∀conf s v p1 p2 e d tl ds.
    p1 ≠ p2
    ∧ qlk s.queues p1 = d::tl
    ∧ final d
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2
                        (s with <|queues :=
                                    normalise_queues(s.queues   |+ (p1,tl));
                                  bindings :=
                                    s.bindings |+ (v,FLAT(SNOC (unpad d) ds))
                                  |>)
                        e)) ∧

  (* Dequeue-intermediate-payload *)
  (∀conf s v p1 p2 e d tl ds.
    p1 ≠ p2
    ∧ qlk s.queues p1 = d::tl
    ∧ intermediate d
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2 (s with queues :=
                                    normalise_queues(s.queues |+ (p1,tl)))
                           (Receive p1 v (SNOC (unpad d) ds) e))) ∧

  (* If-L *)
  (∀conf s v p e1 e2.
    FLOOKUP s.bindings v = SOME [1w]
    ⇒ trans conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e1)) ∧

  (* If-R *)
  (∀conf s v p e1 e2 w.
    FLOOKUP s.bindings v = SOME w ∧ w ≠ [1w]
    ⇒ trans conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e2)) ∧

  (* Let *)
  (∀conf s v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ⇒ trans conf (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p
                        (s with bindings :=
                          s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl)))
                        e)) ∧

  (* Par-L *)
  (∀conf n1 n1' n2 α.
    trans conf n1 α n1'
    ⇒ trans conf (NPar n1 n2)
             α
             (NPar n1' n2)) ∧

  (* Par-R *)
  (∀conf n1 n2 n2' α.
    trans conf n2 α n2'
    ⇒ trans conf (NPar n1 n2)
             α
             (NPar n1 n2'))

  (* Recursion *)
∧ (∀conf p s dn e alpha n.
    trans conf (NEndpoint p s (dsubst e dn (Fix dn e))) alpha n
    ⇒ trans conf (NEndpoint p s (Fix dn e)) alpha n)
End

val _ = zip ["trans_send_last_payload","trans_send_intermediate_payload",
             "trans_enqueue","trans_com_l","trans_com_r",
             "trans_dequeue_last_payload","trans_dequeue_intermediate_payload",
             "trans_if_true","trans_if_false","trans_let","trans_par_l","trans_par_r","trans_fix"]
            (CONJUNCTS trans_rules) |> map save_thm;

Definition reduction_def:
  reduction conf p q = trans conf p LTau q
End

Definition weak_tau_trans_def:
  weak_tau_trans conf p alpha q =
    ?p' q'. (reduction conf)^* p p' ∧ trans conf p' alpha q' ∧ (reduction conf)^* q' q
End

Definition weak_trans_def:
  weak_trans conf p alpha q =
    if alpha = LTau then (reduction conf)^* p q else weak_tau_trans conf p alpha q
End

Definition sender_def:
  sender LTau = NONE ∧
  (sender (LReceive p d q) = SOME p) ∧
  (sender (LSend p d q) = SOME p)
End

val _ = export_theory ()
