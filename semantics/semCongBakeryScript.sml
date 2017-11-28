open preamble

open astBakeryTheory

(* Semantics with build-in congruence *)
val _ = new_theory "semCongBakery";

val _ = Datatype`
  label = LTau proc (varN option)
        | LCom proc varN proc varN
        | LSel proc bool proc
`;

val freeprocs_def = Define`
  freeprocs (LTau p v)          = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
`;

val sender_def = Define`
  sender (LTau p v)          = NONE
∧ sender (LCom p1 v1 p2 v2) = SOME p1
∧ sender (LSel p1 b p2)     = SOME p1
`;

val receiver_def = Define`
  receiver (LTau p v)          = NONE
∧ receiver (LCom p1 v1 p2 v2) = SOME p2
∧ receiver (LSel p1 b p2)     = SOME p2
`;

val written_def = Define`
  written (LTau p NONE)       = NONE
∧ written (LTau p (SOME v))  = SOME(v,p)
∧ written (LCom p1 v1 p2 v2) = SOME(v2,p2)
∧ written (LSel p1 b p2)     = NONE
`;

val (scong_rules, scong_ind, scong_cases) = Hol_reln `
(* Basic congruence rules *)

  (* Symmetric *)
  (∀c. scong c c)

  (* Reflexive *)
∧ (∀c1 c2.
    scong c1 c2
    ⇒ scong c2 c1)
  (* Transitive *)
∧ (∀c1 c2 c3.
     scong c1 c2
     ∧ scong c2 c3
     ⇒ scong c1 c3)

(* Swapping rules *)

(* Swapping communications and selections is only posible if the
   processes involved in each operations are diferent (all of them)
*)
∧ (∀p1 p2 p3 p4 v1 v2 v3 v4 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ scong (Com p1 v1 p2 v2 (Com p3 v3 p4 v4 c))
            (Com p3 v3 p4 v4 (Com p1 v1 p2 v2 c)))
∧ (∀p1 p2 p3 p4 v1 v2 v3 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ scong (Com p1 v1 p2 v2 (Sel p3 v3 p4 c))
            (Sel p3 v3 p4 (Com p1 v1 p2 v2 c)))
∧ (∀p1 p2 p3 p4 v1 v3 c.
    {p1;p2} ∩ {p3;p4} = {}
    ⇒ scong (Sel p1 v1 p2 (Sel p3 v3 p4 c))
            (Sel p3 v3 p4 (Sel p1 v1 p2 c)))

(* Let swaps need to make sure no pair of process and variable is
   shared betwen operations (this includes the arguments to the let
   function)
*)
∧ (∀p1 p2 p3 v1 v2 v3 f vl c.
    (p3,v3) ∉ {(p1,v1);(p2,v2)}
    ∧ (p1,v1) ∉ {(p3,i)| i ∈ set vl}
    ∧ (p2,v2) ∉ {(p3,i)| i ∈ set vl}
    ⇒ scong (Com p1 v1 p2 v2 (Let v3 p3 f vl c))
            (Let v3 p3 f vl (Com p1 v1 p2 v2 c)))
∧ (∀v v' p p' f f' vl vl' c.
    (p,v) ≠ (p',v')
    ∧ (p,v) ∉ {(p',i) | i ∈ set vl'}
    ∧ (p',v') ∉ {(p,i) | i ∈ set vl}
   ⇒ scong (Let v p f vl (Let v' p' f' vl' c))
           (Let v' p' f' vl' (Let v p f vl c)))
∧ (∀p1 p2 p3 b v vl f c.
    scong (Sel p1 b p2 (Let v p3 f vl c))
          (Let v p3 f vl (Sel p1 b p2 c)))

(* If Rules *)
∧ (∀p q e1 e2 c1 c2 c1' c2'.
    p ≠ q
    ⇒ scong (IfThen e1 p (IfThen e2 q c1 c2)  (IfThen e2 q c1' c2'))
            (IfThen e2 q (IfThen e1 p c1 c1') (IfThen e1 p c2  c2')))
∧ (∀p1 p2 p v1 v2 c1 c2 e.
    p ∉ {p1;p2}
    ⇒ scong (Com p1 v1 p2 v2 (IfThen e p c1 c2))
            (IfThen e p (Com p1 v1 p2 v2 c1) (Com p1 v1 p2 v2 c2)))
∧ (∀p1 p2 b c1 c2 p e.
    p ∉ {p1;p2}
    ⇒ scong (Sel p1 b p2 (IfThen e p c1 c2))
            (IfThen e p (Sel p1 b p2 c1) (Sel p1 b p2 c2)))
∧ (∀p1 p2 v f vl e c1 c2.
    (p1,v) ≠ (p2,e)
    ⇒ scong (Let v p1 f vl (IfThen e p2 c1 c2))
            (IfThen e p2 (Let v p1 f vl c1) (Let v p1 f vl c2)))

  (* Structural rules *)
∧ (∀p e c1 c1' c2 c2'.
    scong c1 c1'
    ∧ scong c2 c2'
    ⇒ scong (IfThen e p c1 c2) (IfThen e p c1' c2'))
∧ (∀p v f vl c c'.
    scong c c'
    ⇒ scong (Let v p f vl c) (Let v p f vl c'))
∧ (∀p1 v1 p2 v2 c c'.
    scong c c'
    ⇒ scong (Com p1 v1 p2 v2 c) (Com p1 v1 p2 v2 c'))
∧ (∀p1 b p2 c c'.
    scong c c'
    ⇒ scong (Sel p1 b p2 c) (Sel p1 b p2 c'))
`;

val _ = Parse.add_infix("≅",425,Parse.NONASSOC);
val _ = Parse.overload_on("≅",``scong``);

val _ = zip ["scong_sym", "scong_refl", "scong_trans"
            , "scong__com_swap", "scong_com_sel_swap"
            , "scong_sel_swap", "scong_com_let_swap"
            , "scong_let_swap", "scong_sel_let_swap"
            , "scong_if_swap", "scong_com_if_swap"
            , "scong_sel_if_swap", "scong_let_if_swap"
            , "scong_if", "scong_let", "scong_com"
            , "scong_sel"]
            (CONJUNCTS scong_rules) |> map save_thm;

val (transCong_rules,transCong_ind,transCong_cases) = Hol_reln `
  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ∧ p1 ≠ p2
    ⇒ transCong (s,Com p1 v1 p2 v2 c) (LCom p1 v1 p2 v2) (s |+ ((v2,p2),d),c))

  (* Selection *)
∧ (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ transCong (s,Sel p1 b p2 c) (LSel p1 b p2) (s,c))

  (* Let *)
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
    ⇒ transCong (s,Let v p f vl c)
                (LTau p (SOME v))
                (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl))),c))
  (* If (True) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME [1w]
    ⇒ transCong (s,IfThen v p c1 c2) (LTau p NONE) (s,c1))

  (* If (False) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w]
    ⇒ transCong (s,IfThen v p c1 c2) (LTau p NONE) (s,c2))

  (* Asynchrony *)
∧ (∀s c s' c' p1 v1 p2 v2 alpha.
    transCong (s,c) alpha (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ written alpha ≠ SOME (v1,p1)
    ∧ p2 ∉ freeprocs alpha
    ⇒ transCong (s,Com p1 v1 p2 v2 c) alpha (s',Com p1 v1 p2 v2 c'))

∧ (∀s c s' c' p1 b p2 alpha.
    transCong (s,c) alpha (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ transCong (s,Sel p1 b p2 c) alpha (s',Sel p1 b p2 c'))

  (* Congruence *)
∧ (∀c1 c2 c1' c2' alpha.
    c1 ≅ c1'
    ∧ transCong (s,c1') alpha (s',c2')
    ∧ c2' ≅ c2
    ⇒ transCong (s,c1) alpha (s',c2))
`;

val _ = export_theory ()
