open preamble

open astBakeryTheory

(* Semantics with build-in congruence *)
val _ = new_theory "semCongBakery";

val (transCong_rules,transCong_ind,transCong_cases) = Hol_reln `

  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ⇒ transCong (s,Com p1 v1 p2 v2 c) (LCom p1 v2 p2 v2) (s |+ ((v2,p2),d),c))

  (* Selection *)
∧ (∀s p1 b p2 c.
    transCong (s,Sel p1 b p2 c) (LSel p1 v p2) (s,c))

  (* Let *)
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
    ⇒ transCong (s,Let v p f vl c) (LTau p) (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl))),c))

  (* If (True) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME [1w]
    ⇒ transCong (s,IfThen v p c1 c2) (LTau p) (s,c1))

  (* If (False) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w]
    ⇒ transCong (s,IfThen v p c1 c2) (LTau p) (s,c2))

  (* Asynchrony *)
∧ (∀s c s' c' p1 v1 p2 v2 p p'.
    transCong (s,c) alpha (s',c')
    ∧ sender alpha = SOME p
    ∧ receiver alpha = SOME p'
    ∧ p ∈ {p1;p2}
    ∧ p' ∉ {p1;p2}
    ⇒ transCong (s,Com p1 v1 p2 v2 c) alpha (s',Com p1 v1 p2 v2 c'))
`;

(* Reflexive transCongitive closure *)
val (transCong_s_rules,transCong_s_ind,transCong_s_cases) = Hol_reln `
  (∀s s' e1 e2.
    transCong (s,e1) alpha (s',e2)
    ⇒ transCong_s (s,e1) (s',e2))
∧ (∀s s' s'' e1 e2 e3.
    transCong (s,e1) alpha (s',e2)
    ∧ transCong_s (s',e2) (s'',e3)
  ⇒ transCong_s (s,e1) (s'',e3))
`;

val _ = export_theory ()
