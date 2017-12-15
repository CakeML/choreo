open preamble payloadLangTheory

val _ = new_theory "payloadSemantics";

val _ = Datatype `
 label = LSend proc datum proc
       | LReceive proc datum proc
       | LIntChoice proc bool proc
       | LExtChoice proc bool proc
       | LTau
`

val (trans_rules,trans_ind,trans_cases) = Hol_reln `

  (* Send-var *)
  (∀conf s v d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 (INL v) e)) (LTau) (NEndpoint p1 s (Send p2 (INR d) e)))

  (* Send-last-payload *)
∧ (∀conf s d p1 p2 e.
    LENGTH d <= conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 (INR d) e)) (LSend p1 (6w::d) p2) (NEndpoint p1 s e))

  (* Send-intermediate-payload *)
∧ (∀conf s d p1 p2 e.
    LENGTH d > conf.payload_size
    ∧ p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (Send p2 (INR d) e))
                  (LSend p1 (2w::TAKE conf.payload_size d) p2)
                  (NEndpoint p1 s (Send p2 (INR (DROP conf.payload_size d)) e)))

  (* Enqueue *)
∧ (∀conf s d p1 p2 e.
    p1 ≠ p2
    ⇒ trans conf (NEndpoint p2 s e)
             (LReceive p1 d p2)
             (NEndpoint p2 (s with queue := SNOC (p1,d) s.queue) e))

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

  (* IntChoice *)
∧ (∀conf s b p1 p2 e.
    p1 ≠ p2
    ⇒ trans conf (NEndpoint p1 s (IntChoice b p2 e)) (LIntChoice p1 b p2) (NEndpoint p1 s e))

  (* Enqueue-Choice-L *)
∧ (∀conf s p1 p2 e.
    p1 ≠ p2
    ⇒ trans conf (NEndpoint p2 s e)
             (LExtChoice p1 T p2)
             (NEndpoint p2 (s with queue := SNOC (p1,[6w;1w]) s.queue) e))

  (* Enqueue-Choice-R *)
∧ (∀conf s p1 p2 e.
    p1 ≠ p2
    ⇒ trans conf (NEndpoint p2 s e)
             (LExtChoice p1 F p2)
             (NEndpoint p2 (s with queue := SNOC (p1,[6w;0w]) s.queue) e))

  (* Com-Choice-L *)
∧ (∀conf n1 n2 p1 p2 b n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LIntChoice p1 b p2) n1'
    ∧ trans conf n2 (LExtChoice p1 b p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-Choice-R *)
∧ (∀conf n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans conf n1 (LExtChoice p1 d p2) n1'
    ∧ trans conf n2 (LIntChoice p1 d p2) n2'
    ⇒ trans conf (NPar n1 n2) LTau (NPar n1' n2'))

  (* Dequeue-last-payload *)
∧ (∀conf s v p1 p2 e q1 q2 d ds.
    s.queue = q1 ++ [(p1,6w::d)] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1 
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2 (s with <|queue := q1 ++ q2;
                                     bindings := s.bindings |+ (v,FLAT(SNOC d ds))|>) e))

  (* Dequeue-intermediate-payload *)
∧ (∀conf s v p1 p2 e q1 q2 d ds.
    s.queue = q1 ++ [(p1,2w::d)] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1 
    ⇒ trans conf (NEndpoint p2 s (Receive p1 v ds e))
             LTau
             (NEndpoint p2 (s with queue := q1 ++ q2) (Receive p1 v (SNOC d ds) e)))

  (* ExtChoice-L *)
∧ (∀conf s p1 p2 e1 e2 q1 q2.
    s.queue = q1 ++ [(p1,[6w;1w])] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1 
    ⇒ trans conf (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 (s with queue := q1 ++ q2) e1))

  (* ExtChoice-R *)
∧ (∀conf s p1 p2 e1 e2 q1 q2.
    s.queue = q1 ++ [(p1,[6w;0w])] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1 
    ⇒ trans conf (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 (s with queue := q1 ++ q2) e2))

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

 val _ = zip ["trans_send_var","trans_send_last_payload","trans_send_intermediate_payload",
              "trans_enqueue","trans_com_l","trans_com_r","trans_int_choice",
              "trans_enqueue_choice_l","trans_enqueue_choice_r","trans_com_choice_l","trans_com_choice_r",
              "trans_dequeue_last_payload","trans_dequeue_intermediate_payload",
              "trans_ext_choice_l","trans_ext_choice_r",
              "trans_if_true","trans_if_false","trans_let","trans_par_l","trans_par_r"]
            (CONJUNCTS trans_rules) |> map save_thm;

val reduction_def = Define `
  reduction conf p q = trans conf p LTau q`

val _ = export_theory ()
