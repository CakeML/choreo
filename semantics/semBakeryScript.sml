open preamble

open astBakeryTheory

val _ = new_theory "semBakery";

val _ = Datatype`
  label = LTau proc varN
        | LCom proc varN proc varN
        | LSel proc bool proc
        | LLet varN proc (datum list -> datum) (varN list)
`;

val freeprocs_def = Define`
  freeprocs (LTau p n)         = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LLet v p f vl)     = {p}
`;

val sender_def = Define`
  sender (LTau p n)         = NONE
∧ sender (LCom p1 v1 p2 v2) = SOME p1
∧ sender (LSel p1 b p2)     = SOME p1
∧ sender (LLet v p f vl)     = NONE
`;

val receiver_def = Define`
  receiver (LTau p n)          = NONE
∧ receiver (LCom p1 v1 p2 v2) = SOME p2
∧ receiver (LSel p1 b p2)     = SOME p2
∧ receiver (LLet v p f vl)     = NONE
`;

val written_def = Define`
  written (LTau p n)          = NONE
∧ written (LCom p1 v1 p2 v2) = SOME(v2,p2)
∧ written (LSel p1 b p2)     = NONE
∧ written (LLet v p f vl)     = SOME(v,p)
`;

val read_def = Define`
  read (LTau p n)          = {(n,p)}
∧ read (LCom p1 v1 p2 v2) = {(v1,p1)}
∧ read (LSel p1 b p2)     = {}
∧ read (LLet v p f vl)     = set(MAP (λv. (v,p)) vl)
`;

(*val written_value_def = Define`
   written_value s (LTau p n) = NONE
∧ written_value s (LCom p1 v1 p2 v2) = FLOOKUP s (v1,p1)
∧ written_value s (LSel p1 b p2)     = NONE
∧ written_value s (LLet v p f vl)     = SOME(f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl)))
`*)

val (trans_rules,trans_ind,trans_cases) = Hol_reln `

  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ∧ p1 ≠ p2
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LCom p1 v1 p2 v2,[]) (s |+ ((v2,p2),d),c))

  (* Selection *)
∧ (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ trans (s,Sel p1 b p2 c) (LSel p1 b p2,[]) (s,c))

  (* Let *)
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
    ⇒ trans (s,Let v p f vl c)
            (LLet v p f vl,[])
            (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl))),c))

  (* If (True) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c1))

  (* If (False) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c2))

  (* Swapping transitions / Structural congruence *)
∧ (∀s v p c1 c2 s' c1' c2' l alpha.
    trans (s,c1) (alpha,l) (s',c1')
    ∧ trans (s,c2) (alpha,l) (s',c2')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,IfThen v p c1 c2) (alpha,l) (s',IfThen v p c1' c2'))
∧ (∀s c s' c' p1 v1 p2 v2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,l) (s',Com p1 v1 p2 v2 c'))
∧ (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,l) (s',Sel p1 b p2 c'))
∧ (∀s c s' c' p v f vl l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,Let v p f vl c) (alpha,l) (s',Let v p f vl c'))

  (* Asynchrony *)
∧ (∀s c s' c' p1 v1 p2 v2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ written alpha ≠ SOME (v1,p1)
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,LCom p1 v1 p2 v2::l) (s',Com p1 v1 p2 v2 c'))

∧ (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,LSel p1 b p2::l) (s',Sel p1 b p2 c'))

`;

val _ = zip ["trans_com","trans_sel","trans_let","trans_if_true","trans_if_false",
              "trans_if_swap","trans_com_swap","trans_sel_swap","trans_let_swap",
              "trans_com_async","trans_sel_async"]
            (CONJUNCTS trans_rules) |> map save_thm;

val trans_pairind = save_thm("trans_pairind",
  theorem"trans_strongind"
  |> Q.SPEC `λa0 a1 a2. P (FST a0) (SND a0) (FST a1) (SND a1)  (FST a2) (SND a2)`
  |> SIMP_RULE std_ss [FORALL_PROD]
  |> Q.GEN `P`
);

(* valid_action ensures a transition tag `alpha` and an asyncronous
   transition tag `h` are related as described in the asyncronous
   transitions rules (trans_com_async and trans_sel_async).

   For this relation to hold `h` must:

   * Be one of LSel or LCom

   * Have its sender be a free process in `alpha`

   * Don't have as a receiver a free process in `alpha`
*)
val valid_action_def = Define`
  valid_action alpha h = ((∃p1 b p2 .
                           h = LSel p1 b p2
                           ∧ p1 ∈ freeprocs alpha
                           ∧ p2 ∉ freeprocs alpha) ∨
                          (∃p1 v1 p2 v2.
                            h = LCom p1 v1 p2 v2
                            ∧ p1 ∈ freeprocs alpha
                            ∧ p2 ∉ freeprocs alpha))
`;

(* Any valid transition ensures the relationship between the
   transition tag `t` and the head of the asyncronous transitions list
   `h` is a valid_action
*)
val trans_valid_action = Q.store_thm("trans_valid_action",
  `∀s c s' c' t h l.
    trans (s,c) (t,h::l) (s',c')
    ⇒ valid_action t h`,
  rpt GEN_TAC
  \\ `∀s c t l' s' c'.
        trans (s,c) (t,l') (s',c')
        ⇒ l' = h::l
        ⇒ valid_action t h`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [trans_rules,valid_action_def]
  \\ rfs [freeprocs_def, sender_def, receiver_def]
);

(* Any valid trasition with a non-empty list of asyncronous trasitions
   implies there exist a transition with the same transition tag
   and the tail of the asyncronous transition list
*)
val trans_async_some_trans = Q.store_thm("trans_async_some_trans",
  `∀s c s' c' t h l.
    trans (s,c) (t,h::l) (s',c')
    ⇒ ∃s1 c1 s1' c1'. trans (s1,c1) (t,l) (s1',c1')`,
  rpt GEN_TAC
  \\ `∀s c t l' s' c'.
        trans (s,c) (t,l') (s',c')
        ⇒ l' = h::l
        ⇒ ∃s1 c1 s1' c1'. trans (s1,c1) (t,l) (s1',c1')`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [trans_rules]
  \\ metis_tac []
);

(* valid_actions over a list of actions *)
val valid_actions_def   = Define`
  valid_actions alpha l = EVERY (valid_action alpha) l
`;


(* Any valid transition ensures that both transition tag `t` and
   asyncronous transitions list `l` satisfies valid_actions
*)
val trans_valid_actions = Q.store_thm("trans_valid_actions",
  `∀s c s' c' t l.
    trans (s,c) (t,l) (s',c')
    ⇒ valid_actions t l`,
  Induct_on `l` >> rw []
  >- rw [valid_actions_def]
  \\ IMP_RES_TAC trans_valid_action
  \\ IMP_RES_TAC trans_async_some_trans
  \\ `valid_actions t l` by metis_tac []
  \\ fs [valid_actions_def]
);

(* Reflexive transitive closure *)
val trans_s_def = Define`
  trans_s = RTC (λp q. ∃s. trans p s q)
`;

val _ = export_theory ()
