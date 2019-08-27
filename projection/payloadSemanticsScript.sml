open preamble payloadLangTheory

val _ = new_theory "payloadSemantics";

Definition FGET_def:
  FGET fm dv k =
    case FLOOKUP fm k of
      SOME kv => kv
    | NONE    => dv
End

val _ = Datatype `
 label = LSend proc datum proc
       | LReceive proc datum proc
       | LTau
`

val (trans_rules,trans_ind,trans_cases) = Hol_reln `

  (* Send-last-payload *)
  (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n <= conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 v n e)) (LSend p1 (pad conf (DROP n d)) p2) (NEndpoint p1 s e))

  (* Send-intermediate-payload *)
∧ (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n > conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 v n e))
                  (LSend p1 (pad conf (DROP n d)) p2)
                  (NEndpoint p1 s (Send p2 v (n + conf.payload_size) e)))

  (* Enqueue *)
∧ (∀conf s d p1 p2 e.
    p1 ≠ p2
    ⇒ trans conf (NEndpoint p2 s e)
             (LReceive p1 d p2)
             (NEndpoint p2 (s with queues := s.queues |+ (p1, SNOC d (FGET s.queues [] p1))) e))

  (* Com-L *)
∧ (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LSend p1 d p2) n1'
    ∧ trans conf n2 (LReceive p1 d p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-R *)
∧ (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LReceive p1 d p2) n1'
    ∧ trans conf n2 (LSend p1 d p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2'))

  (* Dequeue-last-payload *)
∧ (∀conf s v p1 p2 e d tl ds.
    p1 ≠ p2
    ∧ FLOOKUP s.queues p1 = SOME (d::tl)
    ∧ final d
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2 (s with <|queues :=  s.queues |+ (p1,tl);
                                     bindings := s.bindings |+ (v,FLAT(SNOC (unpad d) ds))|>) e))

  (* Dequeue-intermediate-payload *)
∧ (∀conf s v p1 p2 e d tl ds.
    p1 ≠ p2
    ∧ FLOOKUP s.queues p1 = SOME (d::tl) 
    ∧ intermediate d
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2 (s with queues := s.queues |+ (p1,tl)) (Receive p1 v (SNOC (unpad d) ds) e)))

  (* If-L *)
∧ (∀conf s v p e1 e2.
    FLOOKUP s.bindings v = SOME [1w]
    ⇒ trans conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e1))

  (* If-R *)
∧ (∀conf s v p e1 e2 w.
    FLOOKUP s.bindings v = SOME w ∧ w ≠ [1w]
    ⇒ trans conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e2))

  (* Let *)
∧ (∀conf s v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ⇒ trans conf (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p (s with bindings := s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl))) e))

  (* Par-L *)
∧ (∀conf n1 n1' n2 alpha.
    trans conf n1 alpha n1'
    ⇒ trans conf (NPar n1 n2)
             alpha
             (NPar n1' n2))

  (* Par-R *)
∧ (∀conf n1 n2 n2' alpha.
    trans conf n2 alpha n2'
    ⇒ trans conf (NPar n1 n2)
             alpha
             (NPar n1 n2'))
`

 val _ = zip ["trans_send_last_payload","trans_send_intermediate_payload",
              "trans_enqueue","trans_com_l","trans_com_r",
              "trans_dequeue_last_payload","trans_dequeue_intermediate_payload",
              "trans_if_true","trans_if_false","trans_let","trans_par_l","trans_par_r"]
            (CONJUNCTS trans_rules) |> map save_thm;

val reduction_def = Define `
  reduction conf p q = trans conf p LTau q`

val weak_tau_trans_def = Define `
  weak_tau_trans conf p alpha q =
    ?p' q'. (reduction conf)^* p p' /\ trans conf p' alpha q' /\ (reduction conf)^* q' q`

val weak_trans_def = Define `
  weak_trans conf p alpha q =
    if alpha = LTau then (reduction conf)^* p q else weak_tau_trans conf p alpha q`

val _ = export_theory ()
