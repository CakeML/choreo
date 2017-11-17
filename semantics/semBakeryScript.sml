open preamble

open astBakeryTheory baseSemBakeryTheory

val _ = new_theory "semBakery";

val (trans_rules,trans_ind,trans_cases) = Hol_reln `

  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LCom p1 v2 p2 v2) (s |+ ((v2,p2),d),c))

  (* Selection *)
∧ (∀s p1 b p2 c.
    trans (s,Sel p1 b p2 c) (LSel p1 v p2) (s,c))

  (* Let *)
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
    /\ trans (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl))),c) alpha (s',c')
    ⇒ trans (s,Let v p f vl c) alpha (s',c'))

  (* If (True) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p) (s,c1))

  (* If (False) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p) (s,c2))

  (* Swapping transitions / Structural congruence *)
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
`;

(* Reflexive transitive closure *)
val trans_s_def = Define`
  trans_s = RTC (λp q. ∃s. trans p s q)
`;

val _ = export_theory ()
