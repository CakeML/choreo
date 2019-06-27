open preamble

open astHalfBakeryTheory

val _ = new_theory "semHalfBakery";

val _ = Datatype`
  label = LTau proc varN
        | LCom proc varN proc varN
        | LComSend proc varN proc varN
        | LComRecv proc varN (proc#datum)
        | LSel proc bool proc
        | LSelSend proc bool proc
        | LSelRecv proc bool proc
        | LLet varN proc (datum list -> datum) (varN list)
`;

val freeprocs_def = Define`
  freeprocs (LTau p n)             = {p}
∧ freeprocs (LCom p1 v1 p2 v2)     = {p1;p2}
∧ freeprocs (LSel p1 b p2)         = {p1;p2}
∧ freeprocs (LSel p1 b p2)         = {p1;p2}
∧ freeprocs (LLet v p f vl)        = {p}
∧ freeprocs (LComSend p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSelSend p1 b p2)     = {p1;p2}
∧ freeprocs (LComRecv p v _)       = {p}
∧ freeprocs (LSelRecv p b _)       = {p}
`;

val sender_def = Define`
  sender (LTau p n)             = NONE
∧ sender (LCom p1 v1 p2 v2)     = SOME p1
∧ sender (LSel p1 b p2)         = SOME p1
∧ sender (LLet v p f vl)        = NONE
∧ sender (LComSend p1 v1 p2 v2) = SOME p1
∧ sender (LSelSend p1 b p2)     = SOME p1
∧ sender (LComRecv p1 v1 _)     = NONE
∧ sender (LSelRecv p1 b1 _)     = NONE
`;

val receiver_def = Define`
  receiver (LTau p n)              = NONE
∧ receiver (LCom p1 v1 p2 v2)      = SOME p2
∧ receiver (LSel p1 b p2)          = SOME p2
∧ receiver (LLet v p f vl)         = NONE
∧ receiver (LComSend p1 v1 p2 v2)  = SOME p2
∧ receiver (LSelSend p1 b p2)      = SOME p2
∧ receiver (LComRecv p1 v1 _)      = SOME p1
∧ receiver (LSelRecv p1 b1 _)      = SOME p1
`;

val written_def = Define`
  written (LTau p n)             = NONE
∧ written (LCom p1 v1 p2 v2)     = SOME(v2,p2)
∧ written (LSel p1 b p2)         = NONE
∧ written (LLet v p f vl)        = SOME(v,p)
∧ written (LComSend p1 v1 p2 v2) = NONE
∧ written (LSelSend p1 b p2)     = NONE
∧ written (LComRecv p v _)       = SOME (v,p)
∧ written (LSelRecv p b _)       = NONE
`;

val read_def = Define`
  read (LTau p n)             = {(n,p)}
∧ read (LCom p1 v1 p2 v2)     = {(v1,p1)}
∧ read (LSel p1 b p2)         = {}
∧ read (LLet v p f vl)        = set(MAP (λv. (v,p)) vl)
∧ read (LComSend p1 v1 p2 v2) = {(v1,p1)}
∧ read (LSelSend p1 b p2)     = {}
∧ read (LComRecv p v _)       = {}
∧ read (LSelRecv p b _)       = {}
`;

(* The set of all processes in a choreography *)
val procsOf_def = Define`
  procsOf  Nil               = []
∧ procsOf (IfThen _ p l r)   = nub ([p] ++ procsOf l ++ procsOf r)
∧ procsOf (Com p _ q _ c)    = nub ([p;q] ++ procsOf c)
∧ procsOf (PCom q _ (p,_) c) = nub ([p;q] ++ procsOf c)
∧ procsOf (Sel p _ q c)      = nub ([p;q] ++ procsOf c)
∧ procsOf (PSel q (p,_) c)   = nub ([p;q] ++ procsOf c)
∧ procsOf (Let _ p _ _ c)    = nub ([p]   ++ procsOf c)
`;

Theorem procsOf_all_distinct:
  ∀c. ALL_DISTINCT (procsOf c)
Proof
  Induct_on `c`
  \\ rw [procsOf_def,ALL_DISTINCT,all_distinct_nub]
  \\ PairCases_on `p0`
  \\ rw [procsOf_def,ALL_DISTINCT,all_distinct_nub]
QED

val (trans_rules,trans_ind,trans_cases) = Hol_reln `

  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ∧ p1 ≠ p2
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LCom p1 v1 p2 v2) (s |+ ((v2,p2),d),c))

  (* Partial communication *)
∧ (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ∧ p1 ≠ p2
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LComSend p1 v1 p2 v2) (s,PCom p2 v2 (p1,d) c))

  (* Receive communication *)
∧ (∀s p1 v2 p2 d c.
    p1 ≠ p2
    ⇒ trans (s,PCom p2 v2 (p1,d) c) (LComRecv p2 v2 (p1,d)) (s |+ ((v2,p2),d),c))

  (* Selection *)
∧ (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ trans (s,Sel p1 b p2 c) (LSel p1 b p2) (s,c))

  (* Partial selection *)
∧ (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ trans (s,Sel p1 b p2 c) (LSelSend p1 b p2) (s,PSel p2 (p1,b) c))

  (* Receive selection *)
∧ (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ trans (s,PSel p2 (p1,b) c) (LSelRecv p2 b p1) (s,c))

  (* Let *)
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
    ⇒ trans (s,Let v p f vl c)
            (LLet v p f vl)
            (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl))),c))

  (* If (True) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v) (s,c1))

  (* If (False) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v) (s,c2))

  (* Swapping transitions / Structural congruence *)
∧ (∀s v p c1 c2 s' c1' c2' alpha.
    trans (s,c1) alpha (s',c1')
    ∧ trans (s,c2) alpha (s',c2')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,IfThen v p c1 c2) alpha (s',IfThen v p c1' c2'))
∧ (∀s c s' c' p1 v1 p2 v2 alpha.
    trans (s,c) alpha (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) alpha (s',Com p1 v1 p2 v2 c'))
∧ (∀s c s' c' p1 b p2 alpha.
    trans (s,c) alpha (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) alpha (s',Sel p1 b p2 c'))
∧ (∀s c s' c' p v f vl alpha.
    trans (s,c) alpha (s',c')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,Let v p f vl c) alpha (s',Let v p f vl c'))
`;

val _ = zip [ "trans_com","trans_com_send","trans_com_recv"
            , "trans_sel","trans_sel_send","trans_sel_recv"
            , "trans_let","trans_if_true","trans_if_false"
            , "trans_if_swap"
            , "trans_com_swap"
            , "trans_sel_swap"
            , "trans_let_swap"
              ]
            (CONJUNCTS trans_rules) |> map save_thm;

val trans_pairind = save_thm("trans_pairind",
  theorem"trans_strongind"
  |> Q.SPEC `λa0 a1 a2. P (FST a0) (SND a0) a1  (FST a2) (SND a2)`
  |> SIMP_RULE std_ss [FORALL_PROD]
  |> Q.GEN `P`
);

(* Reflexive transitive closure *)
val trans_s_def = Define`
  trans_s = RTC (λp q. ∃s. trans p s q)
`;

val _ = export_theory ()
