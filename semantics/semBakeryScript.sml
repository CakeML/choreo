open preamble basis

open astBakeryTheory

val _ = new_theory "semBakery";

val freeprocs_def = Define`
  freeprocs (LTau p)           = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
`;

val sender_def = Define`
  sender (LTau p)           = NONE
∧ sender (LCom p1 v1 p2 v2) = SOME p1
∧ sender (LSel p1 b p2)     = SOME p1
`;

val receiver_def = Define`
  receiver (LTau p)           = NONE
∧ receiver (LCom p1 v1 p2 v2) = SOME p2
∧ receiver (LSel p1 b p2)     = SOME p2
`;

val (trans_rules,trans_ind,trans_cases) = Hol_reln `
(∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LCom p1 v2 p2 v2) (s |+ ((v2,p2),d),c))
∧ (∀s p1 b p2 c.
    trans (s,Sel p1 b p2 c) (LSel p1 v p2) (s,c))
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
    ⇒ trans (s,Let v p f vl c) (LTau p) (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl))),c))
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p) (s,c1))
(* Swapping transitions *)
∧ (∀s v p c1 c2 s' c1' c2'.
    trans (s,c1) alpha (s',c1')

    ∧ trans (s,c2) alpha (s',c2')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,IfThen v p c1 c2) alpha (s',IfThen v p c1' c2'))
∧ (∀s c s' c' p1 v1 p2 v2.
    trans (s,c) alpha (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) alpha (s',Com p1 v1 p2 v2 c'))
∧ (∀s c s' c' p1 b p2.
    trans (s,c) alpha (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) alpha (s',Sel p1 b p2 c'))
∧ (∀s c s' c' p v f vl.
    trans (s,c) alpha (s',c')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,Let v p f vl c) alpha (s',Let v p f vl c'))
(* Asynchrony *)
∧ (∀s c s' c' p1 v1 p2 v2 p p'.
    trans (s,c) alpha (s',c')
    ∧ sender alpha = SOME p
    ∧ receiver alpha = SOME p'
    ∧ p ∈ {p1;p2}
    ∧ p' ∉ {p1;p2}
    ⇒ trans (s,Com p1 v1 p2 v2 c) alpha (s',Com p1 v1 p2 v2 c'))
`
val _ = export_theory ()
