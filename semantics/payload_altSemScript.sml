open preamble payloadLangTheory payloadSemTheory

val _ = new_theory "payload_altSem";

Inductive trans_alt:
  (* Send-last-payload *)
  (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n <= conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans_alt conf (NEndpoint p1 s (Send p2 v n e))
                 (LSend p1 (pad conf (DROP n d)) p2)
                 (NEndpoint p1 s e)) ∧

  (* Send-intermediate-payload *)
  (∀conf s v n d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ LENGTH d - n > conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans_alt conf (NEndpoint p1 s (Send p2 v n e))
                  (LSend p1 (pad conf (DROP n d)) p2)
                  (NEndpoint p1 s (Send p2 v (n + conf.payload_size) e))) ∧

  (* Enqueue *)
  (∀conf s d p1 p2 e.
    p1 ≠ p2
    ⇒ trans_alt conf (NEndpoint p2 s e)
             (LReceive p1 d p2)
             (NEndpoint p2 (s with queues := qpush s.queues p1 d) e)) ∧

  (* Com-L *)
  (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans_alt conf n1 (LSend p1 d p2) n1'
    ∧ trans_alt conf n2 (LReceive p1 d p2) n2'
    ⇒ trans_alt conf (NPar n1 n2) LTau (NPar n1' n2')) ∧

  (* Com-R *)
  (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans_alt conf n1 (LReceive p1 d p2) n1'
    ∧ trans_alt conf n2 (LSend p1 d p2) n2'
    ⇒ trans_alt conf (NPar n1 n2) LTau (NPar n1' n2')) ∧

  (* Dequeue-last-payload *)
  (∀conf s v p1 p2 e d tl ds.
    p1 ≠ p2
    ∧ qlk s.queues p1 = d::tl
    ∧ final d
    ⇒ trans_alt conf (NEndpoint p2 s (Receive p1 v ds e))
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
    ⇒ trans_alt conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2 (s with queues :=
                                    normalise_queues(s.queues |+ (p1,tl)))
                           (Receive p1 v (SNOC (unpad d) ds) e))) ∧

  (* If-L *)
  (∀conf s v p e1 e2.
    FLOOKUP s.bindings v = SOME [1w]
    ⇒ trans_alt conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e1)) ∧

  (* If-R *)
  (∀conf s v p e1 e2 w.
    FLOOKUP s.bindings v = SOME w ∧ w ≠ [1w]
    ⇒ trans_alt conf (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e2)) ∧

  (* Let *)
  (∀conf s v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ⇒ trans_alt conf (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p
                        (s with bindings :=
                          s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl)))
                        e)) ∧

  (* Par-L *)
  (∀conf n1 n1' n2 α.
    trans_alt conf n1 α n1'
    ⇒ trans_alt conf (NPar n1 n2)
             α
             (NPar n1' n2)) ∧

  (* Par-R *)
  (∀conf n1 n2 n2' α.
    trans_alt conf n2 α n2'
    ⇒ trans_alt conf (NPar n1 n2)
             α
             (NPar n1 n2'))

  (* Recursion, fixpoint style *)
∧ (∀conf p s dn e.
    trans_alt conf (NEndpoint p s (Fix dn e)) LTau (NEndpoint p s (dsubst e dn (Fix dn e))))

  (* Recursion, letrec style *)
∧ (∀conf p s dn vars e.
    EVERY (IS_SOME o FLOOKUP s.bindings) vars ⇒
    trans_alt conf
          (NEndpoint p s (Letrec dn vars e (FCall dn vars)))
          LTau
          (NEndpoint p
            (s with <|funs := (dn,Closure vars (s.funs,s.bindings) e1)::s.funs|>) e))

∧ (∀conf p s dn args params funs bindings e.
    ALOOKUP s.funs dn = SOME(Closure params (funs,bindings) e) ∧
    LENGTH args = LENGTH params ∧
    EVERY (IS_SOME o FLOOKUP s.bindings) args
    ⇒
    trans conf
          (NEndpoint p s (FCall dn args))
          LTau
          (NEndpoint p (s with <|bindings := bindings |++ ZIP(params,MAP (THE o FLOOKUP s.bindings) args);
                                 funs := (dn,Closure params (funs,bindings) e)::funs|>) e))
End

val _ = zip ["trans_alt_send_last_payload","trans_alt_send_intermediate_payload",
             "trans_alt_enqueue","trans_alt_com_l","trans_alt_com_r",
             "trans_alt_dequeue_last_payload","trans_alt_dequeue_intermediate_payload",
             "trans_alt_if_true","trans_alt_if_false","trans_alt_let","trans_alt_par_l","trans_alt_par_r","trans_alt_fix",
             "trans_alt_letcall","trans_alt_call"]
            (CONJUNCTS trans_alt_rules) |> map save_thm;

Definition reduction_alt_def:
  reduction_alt conf p q = trans_alt conf p LTau q
End

Definition weak_tau_trans_alt_def:
  weak_tau_trans_alt conf p alpha q =
    ?p' q'. (reduction_alt conf)^* p p' ∧ trans_alt conf p' alpha q' ∧ (reduction_alt conf)^* q' q
End

Definition weak_trans_alt_def:
  weak_trans_alt conf p alpha q =
    if alpha = LTau then (reduction_alt conf)^* p q else weak_tau_trans_alt conf p alpha q
End

val _ = export_theory ()
