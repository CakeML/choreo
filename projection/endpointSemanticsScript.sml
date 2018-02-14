open preamble endpointLangTheory

val _ = new_theory "endpointSemantics";

val _ = Datatype `
 label = LSend proc datum proc
       | LReceive proc datum proc
       | LIntChoice proc bool proc
       | LExtChoice proc bool proc
       | LTau
`

val (trans_rules,trans_ind,trans_cases) = Hol_reln `

  (* Send *)
  (∀s v d p1 p2 e.
    FLOOKUP s.bindings v = SOME d
    ∧ p1 ≠ p2
    ⇒ trans (NEndpoint p1 s (Send p2 v e)) (LSend p1 d p2) (NEndpoint p1 s e))

  (* Enqueue *)
∧ (∀s d p1 p2 e.
    p1 ≠ p2
    ⇒ trans (NEndpoint p2 s e)
             (LReceive p1 d p2)
             (NEndpoint p2 (s with queue := SNOC (p1,d) s.queue) e))

  (* Com-L *)
∧ (∀n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans n1 (LSend p1 d p2) n1'
    ∧ trans n2 (LReceive p1 d p2) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-R *)
∧ (∀n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans n1 (LReceive p1 d p2) n1'
    ∧ trans n2 (LSend p1 d p2) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* IntChoice *)
∧ (∀s b p1 p2 e.
    p1 ≠ p2
    ⇒ trans (NEndpoint p1 s (IntChoice b p2 e)) (LIntChoice p1 b p2) (NEndpoint p1 s e))

  (* Enqueue-Choice-L *)
∧ (∀s p1 p2 e.
    p1 ≠ p2
    ⇒ trans (NEndpoint p2 s e)
             (LExtChoice p1 T p2)
             (NEndpoint p2 (s with queue := SNOC (p1,[1w]) s.queue) e))

  (* Enqueue-Choice-R *)
∧ (∀s p1 p2 e.
    p1 ≠ p2
    ⇒ trans (NEndpoint p2 s e)
             (LExtChoice p1 F p2)
             (NEndpoint p2 (s with queue := SNOC (p1,[0w]) s.queue) e))

  (* Com-Choice-L *)
∧ (∀n1 n2 p1 p2 b n1' n2'.
    p1 ≠ p2
    ∧ trans n1 (LIntChoice p1 b p2) n1'
    ∧ trans n2 (LExtChoice p1 b p2) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-Choice-R *)
∧ (∀n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans n1 (LExtChoice p1 d p2) n1'
    ∧ trans n2 (LIntChoice p1 d p2) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Dequeue (aka Receive) *)
∧ (∀s v p1 p2 e q1 q2.
    s.queue = q1 ++ [(p1,d)] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1 
    ⇒ trans (NEndpoint p2 s (Receive p1 v e))
             LTau
             (NEndpoint p2 (s with <|queue := q1 ++ q2;
                                     bindings := s.bindings |+ (v,d)|>) e))

  (* ExtChoice-L *)
∧ (∀s p1 p2 e1 e2 q1 q2.
    s.queue = q1 ++ [(p1,[1w])] ++ q2
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1 
    ⇒ trans (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 (s with queue := q1 ++ q2) e1))

  (* ExtChoice-R *)
∧ (∀s p1 p2 e1 e2 q1 d q2.
    s.queue = q1 ++ [(p1,d)] ++ q2
    ∧ d ≠ [1w]
    ∧ p1 ≠ p2
    ∧ EVERY (λ(p,_). p ≠ p1) q1 
    ⇒ trans (NEndpoint p2 s (ExtChoice p1 e1 e2))
             LTau
             (NEndpoint p2 (s with queue := q1 ++ q2) e2))

  (* If-L *)
∧ (∀s v p e1 e2.
    FLOOKUP s.bindings v = SOME [1w]
    ⇒ trans (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e1))

  (* If-R *)
∧ (∀s v p e1 e2 w.
    FLOOKUP s.bindings v = SOME w ∧ w ≠ [1w]
    ⇒ trans (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e2))

  (* Let *)
∧ (∀s v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ⇒ trans (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p (s with bindings := s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl))) e))

  (* Par-L *)
∧ (∀n1 n1' n2 alpha.
    trans n1 alpha n1'
    ⇒ trans (NPar n1 n2)
             alpha
             (NPar n1' n2))

  (* Par-R *)
∧ (∀n1 n2 n2' alpha.
    trans n2 alpha n2'
    ⇒ trans (NPar n1 n2)
             alpha
             (NPar n1 n2'))
`

val _ = zip ["trans_send","trans_enqueue","trans_com_l","trans_com_r","trans_int_choice",
              "trans_enqueue_choice_l","trans_enqueue_choice_r","trans_com_choice_l","trans_com_choice_r",
              "trans_dequeue","trans_ext_choice_l","trans_ext_choice_r",
              "trans_if_true","trans_if_false","trans_let","trans_par_l","trans_par_r"]
            (CONJUNCTS trans_rules) |> map save_thm;

val reduction_def = Define `
  reduction p q = trans p LTau q`

val weak_tau_trans_def = Define `
  weak_tau_trans p alpha q =
    ?p' q'. reduction^* p p' /\ trans p' alpha q' /\ reduction^* q' q`

val weak_trans_def = Define `
  weak_trans p alpha q =
    if alpha = LTau then reduction^* p q else weak_tau_trans p alpha q`

val _ = export_theory ()
