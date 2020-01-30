open preamble

open astBakeryTheory

val _ = new_theory "semBakery";

Datatype:
  label = LTau proc varN
        | LCom proc varN proc varN
        | LSel proc bool proc
        | LLet varN proc (datum list -> datum) (varN list)
End

Definition freeprocs_def:
  freeprocs (LTau p n)         = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LLet v p f vl)     = {p}
End

Definition sender_def:
  sender (LTau p n)          = SOME p
∧ sender (LCom p1 v1 p2 v2)  = SOME p1
∧ sender (LSel p1 b p2)      = SOME p1
∧ sender (LLet v p f vl)     = SOME p
End

Definition receiver_def:
  receiver (LTau p n)          = NONE
∧ receiver (LCom p1 v1 p2 v2) = SOME p2
∧ receiver (LSel p1 b p2)     = SOME p2
∧ receiver (LLet v p f vl)     = NONE
End

Definition written_def:
  written (LTau p n)          = NONE
∧ written (LCom p1 v1 p2 v2) = SOME(v2,p2)
∧ written (LSel p1 b p2)     = NONE
∧ written (LLet v p f vl)     = SOME(v,p)
End

Definition read_def:
  read (LTau p n)          = {(n,p)}
∧ read (LCom p1 v1 p2 v2) = {(v1,p1)}
∧ read (LSel p1 b p2)     = {}
∧ read (LLet v p f vl)     = set(MAP (λv. (v,p)) vl)
End

(* On ListTheory.sml *)
Definition nub'_def:
  nub' []      = []
∧ nub' (x::xs) = x :: FILTER ($≠ x) (nub' xs)
Termination
  WF_REL_TAC `measure LENGTH`
  \\ rw [LENGTH]
  \\ ho_match_mp_tac LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `LENGTH xs`
  \\ rw [LENGTH_FILTER_LEQ]
End

Theorem all_distinct_nub':
  ∀l. ALL_DISTINCT (nub' l)
Proof
  rw [ALL_DISTINCT,nub'_def]
  \\ Induct_on `l`
  \\ rw [ALL_DISTINCT,nub'_def,FILTER_ALL_DISTINCT,MEM_FILTER]
QED

(* The set of all processes in a choreography *)
Definition procsOf_def:
  procsOf  Nil             = []
∧ procsOf (IfThen _ p l r) = nub' ([p] ++ procsOf l ++ procsOf r)
∧ procsOf (Com p _ q _ c)  = nub' ([p;q] ++ procsOf c)
∧ procsOf (Sel p _ q c)    = nub' ([p;q] ++ procsOf c)
∧ procsOf (Let _ p _ _ c)  = nub' ([p] ++ procsOf c)
End

Theorem procsOf_all_distinct:
  ∀c. ALL_DISTINCT (procsOf c)
Proof
  Induct_on `c` >> rw [procsOf_def,ALL_DISTINCT,all_distinct_nub']
QED

Inductive trans:
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
    ∧ sender alpha = SOME p1
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,LCom p1 v1 p2 v2::l) (s',Com p1 v1 p2 v2 c'))

∧ (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ sender alpha = SOME p1
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,LSel p1 b p2::l) (s',Sel p1 b p2 c'))

∧ (∀s c s' c' p1 v1 p2 v2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ receiver alpha = SOME p1
    ∧ sender alpha   ≠ SOME p1
    ∧ written alpha ≠ SOME (v1,p1)
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,l) (s',Com p1 v1 p2 v2 c'))

∧ (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ receiver alpha = SOME p1
    ∧ sender alpha   ≠ SOME p1
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,l) (s',Sel p1 b p2 c'))
End


val _ = zip ["trans_com","trans_sel","trans_let","trans_if_true","trans_if_false",
              "trans_if_swap","trans_com_swap","trans_sel_swap","trans_let_swap",
              "trans_com_send_async","trans_sel_send_async",
              "trans_com_recv_async","trans_sel_recv_async"]
            (CONJUNCTS trans_rules) |> map save_thm;

Theorem trans_pairind =
  theorem"trans_strongind"
  |> Q.SPEC `λa0 a1 a2. P (FST a0) (SND a0) (FST a1) (SND a1)  (FST a2) (SND a2)`
  |> SIMP_RULE std_ss [FORALL_PROD]
  |> Q.GEN `P`

(* valid_action ensures a transition tag `alpha` and an asyncronous
   transition tag `h` are related as described in the asyncronous
   transitions rules (trans_com_async and trans_sel_async).

   For this relation to hold `h` must:

   * Be one of LSel or LCom

   * Have its sender be a free process in `alpha`

   * Don't have as a receiver a free process in `alpha`
*)
Definition valid_action_def:
  valid_action alpha h = ((∃p1 b p2 .
                           h = LSel p1 b p2
                           ∧ p1 ∈ freeprocs alpha
                           ∧ p2 ∉ freeprocs alpha) ∨
                          (∃p1 v1 p2 v2.
                            h = LCom p1 v1 p2 v2
                            ∧ p1 ∈ freeprocs alpha
                            ∧ p2 ∉ freeprocs alpha))
End

(* `lrm l e` removes the first appearance of element `e` in `l` *)
Definition lrm_def:
  lrm [] e      = []
∧ lrm (x::ls) e = (if x = e
                 then ls
                 else x :: lrm ls e)
End

(* If an element `e` is not in `l` then `lrm e l` is redundant *)
Theorem mem_lrm_id:
  ¬ MEM e l ⇒ lrm l e = l
Proof
  Induct_on `l` >> rw [lrm_def,MEM]
QED

(* `lrm` conditionaly distributes over the first argument (`l`) of an
   append if the element you are trying to remove is in `l`
*)
Theorem lrm_mem_append:
  ∀l e r. MEM e l ⇒ lrm (l ++ r) e = lrm l e ++ r
Proof
  induct_on `l` >> rw [MEM,lrm_def]
QED

(* `lrm` conditionaly distributes over the second argument (`r`) of an
   append if the element (`e`) you are trying to remove is not in the
   first argument (`l`). Note that this does not imply that `e` is in
   `r`
*)
Theorem lrm_not_mem_append:
  ∀l e r. ¬ MEM e l ⇒ lrm (l ++ r) e = l ++ lrm r e
Proof
  induct_on `l` >> rw [MEM,lrm_def]
QED

(* Any valid transition ensures the relationship between the
   transition tag `t` and the head of the asyncronous transitions list
   `h` is a valid_action
*)
Theorem trans_valid_action:
   ∀s c s' c' t h l.
    trans (s,c) (t,h::l) (s',c')
    ⇒ valid_action t h
Proof
  rpt GEN_TAC
  \\ `∀s c t l' s' c'.
        trans (s,c) (t,l') (s',c')
        ⇒ l' = h::l
        ⇒ valid_action t h`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [trans_rules,valid_action_def]
  \\ Cases_on ‘t’ \\ fs [sender_def,freeprocs_def]
QED

(* Any valid trasition with a non-empty list of asyncronous trasitions
   implies there exist a transition with the same transition tag
   and the tail of the asyncronous transition list
*)
Theorem trans_async_some_trans:
   ∀s c s' c' t h l.
    trans (s,c) (t,h::l) (s',c')
    ⇒ ∃s1 c1 s1' c1'. trans (s1,c1) (t,l) (s1',c1')
Proof
  rpt GEN_TAC
  \\ `∀s c t l' s' c'.
        trans (s,c) (t,l') (s',c')
        ⇒ l' = h::l
        ⇒ ∃s1 c1 s1' c1'. trans (s1,c1) (t,l) (s1',c1')`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [trans_rules]
  \\ metis_tac []
QED

(* valid_actions over a list of actions *)
Definition valid_actions_def:
  valid_actions alpha l = EVERY (valid_action alpha) l
End


(* Any valid transition ensures that both transition tag `t` and
   asyncronous transitions list `l` satisfies valid_actions
*)
Theorem trans_valid_actions:
   ∀s c s' c' t l.
    trans (s,c) (t,l) (s',c')
    ⇒ valid_actions t l
Proof
  Induct_on `l` >> rw []
  >- rw [valid_actions_def]
  \\ IMP_RES_TAC trans_valid_action
  \\ IMP_RES_TAC trans_async_some_trans
  \\ `valid_actions t l` by metis_tac []
  \\ fs [valid_actions_def]
QED

(* In a list of valid actions (`h`) there are no LTau actions *)
Theorem valid_actions_not_ltau:
  ∀t h p v. valid_actions t h ⇒ ¬ MEM (LTau p v) h
Proof
  rw []
  \\ CCONTR_TAC
  \\ fs [valid_actions_def,EVERY_MEM]
  \\ RES_TAC
  \\ fs [valid_action_def]
QED

(* Reflexive transitive closure *)
Definition trans_s_def:
  trans_s = RTC (λp q. ∃s. trans p s q)
End

(* Give a state and a transition tag, one can generate the resulting state *)
Definition state_from_tag_def:
  state_from_tag s (LCom p1 v1 p2 v2) = (s |+ ((v2,p2),s ' (v1,p1)))
∧ state_from_tag s (LLet v p f vl)  =
    (s |+ ((v,p),f (MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl))))
∧ state_from_tag s _ = s
End

(* The resulting state of any transition can be described using `state_from_tag` *)
Theorem trans_state:
  ∀s c α τ s' c'. trans (s,c) (α,τ) (s',c') ⇒ s' = state_from_tag s α
Proof
  ho_match_mp_tac trans_pairind
  \\ rw [state_from_tag_def]
  \\ fs [FLOOKUP_DEF]
QED

(* Making the state bigger does not affect the behaviour of the choreography *)
Theorem trans_submap:
  ∀s c α τ s' c' z.
   trans (s,c) (α,τ) (s',c') ∧ s ⊑ z
   ⇒ ∃z'. trans (z,c) (α,τ) (z',c') ∧ s' ⊑ z'
Proof
  let
    val local_metis =
      metis_tac [trans_rules,FLOOKUP_SUBMAP,SUBMAP_mono_FUPDATE
                , SUBMAP_DOMSUB,GSYM SUBMAP_DOMSUB_gen
                , SUBMAP_TRANS]
  in
  `∀s c α τ s' c'.
   trans (s,c) (α,τ) (s',c')
   ⇒ ∀z. s ⊑ z
      ⇒ ∃z'. trans (z,c) (α,τ) (z',c') ∧ s' ⊑ z'`
  suffices_by metis_tac []
  \\ ho_match_mp_tac trans_pairind
  \\ rw []
  >- local_metis
  >- local_metis
  >- (`EVERY IS_SOME (MAP (FLOOKUP z) (MAP (λv. (v,p)) vl))`
      by (Induct_on `vl` \\ rw [FLOOKUP_DEF,IS_SOME_DEF]
         \\ rfs [SUBMAP_DEF])
      \\  qexists_tac `z |+ ((v,p),f (MAP (THE ∘ FLOOKUP z) (MAP (λv. (v,p)) vl)))`
      \\ qmatch_goalsub_abbrev_tac `s |+ sl ⊑ z |+ zl`
      \\ `sl = zl` suffices_by local_metis
      \\ unabbrev_all_tac \\ rw [] \\ AP_TERM_TAC
      \\ Induct_on `vl` \\ rw []
      \\ fs [IS_SOME_EXISTS,SUBMAP_DEF,FLOOKUP_SUBMAP,FLOOKUP_DEF])
  >- local_metis
  >- local_metis
  >- (res_tac
     \\ `z' = z''` by metis_tac [trans_state]
     \\ rveq \\ qexists_tac `z'` \\ local_metis)
  \\ local_metis
  end
QED

val RTC_TRANS =  RTC_RULES |> CONV_RULE FORALL_AND_CONV
                           |> CONJUNCTS |> el 2;

(* RTC version of `trans_submap` *)
Theorem trans_s_submap_gen:
  ∀s c α τ s' c' z.
   trans_s (s,c) (s',c') ∧ s ⊑ z
   ⇒ ∃z'. trans_s (z,c) (z',c') ∧ s' ⊑ z'
Proof
  `∀x y. trans_s x y
    ⇒ ∀s c s' c' z. x = (s,c) ∧ y = (s',c') ∧ s ⊑ z
       ⇒ ∃z'. trans_s (z,c) (z',c') ∧ s' ⊑ z'`
  suffices_by metis_tac []
  \\ rewrite_tac [trans_s_def]
  \\ ho_match_mp_tac RTC_INDUCT
  \\ rw []
  >- (qexists_tac `z` \\ rw [])
  \\ PairCases_on `x'` \\ Cases_on `s`
  \\ drule trans_submap
  \\ disch_then drule  \\ rw []
  \\ pop_assum drule   \\ rw []
  \\ qexists_tac `z''` \\ rw []
  \\ ho_match_mp_tac RTC_TRANS
  \\ metis_tac []
QED

(* Slightly more mp-friendly version of `trans_s_submap_gen` *)
Theorem trans_s_submap:
  ∀s c α τ s' c' z.
   trans_s (s,c) (s',c') ∧ s ⊑ z
   ⇒ ∃z'. trans_s (z,c) (z',c')
Proof
  metis_tac [trans_s_submap_gen]
QED

Definition free_variables_def:
  (free_variables (Nil) = {}) /\
  (free_variables (IfThen v p c1 c2) = {(v,p)} ∪ (free_variables c1 ∪ free_variables c2)) /\
  (free_variables (Com p1 v1 p2 v2 c) = {(v1,p1)} ∪ (free_variables c DELETE (v2,p2))) /\
  (free_variables (Let v p f vl c) = set(MAP (λv. (v,p)) vl) ∪ (free_variables c DELETE (v,p))) /\
  (free_variables (Sel p b q c) = free_variables c)
End

Definition defined_vars_def:
  defined_vars (s,c) = FDOM s
End

Definition no_undefined_vars_def:
  no_undefined_vars (s,c) = (free_variables c ⊆ FDOM s)
End

Theorem defined_vars_mono:
  ∀sc alpha sc'. trans sc alpha sc' ⇒ defined_vars sc ⊆ defined_vars sc'
Proof
  ho_match_mp_tac trans_ind
  >> rpt strip_tac
  >> fs[defined_vars_def,SUBSET_OF_INSERT]
QED

Theorem free_vars_mono:
  ∀sc alpha sc'. trans sc alpha sc'
    ⇒ (free_variables(SND sc') DIFF defined_vars sc' ⊆ free_variables(SND sc) DIFF defined_vars sc)
Proof
  ho_match_mp_tac (theorem "trans_strongind")
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> fs[free_variables_def,defined_vars_def,DIFF_INSERT] >> rw[]
  >> fs[DELETE_DEF,DIFF_DEF,SUBSET_DEF] >> rpt strip_tac
  >> fs[] >> metis_tac[]
QED

Theorem no_undefined_vars_trans_pres:
  ∀sc alpha sc'. no_undefined_vars sc ∧ trans sc alpha sc' ⇒ no_undefined_vars sc'
Proof
  rpt gen_tac >> disch_then(MAP_EVERY assume_tac o CONJUNCTS)
  >> qpat_x_assum `no_undefined_vars _` mp_tac
  >> qpat_x_assum `trans _ _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac (theorem "trans_strongind")
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> imp_res_tac free_vars_mono
  >> fs[no_undefined_vars_def,free_variables_def,DELETE_SUBSET_INSERT,defined_vars_def,SUBSET_OF_INSERT]
  >> fs[SUBSET_DEF,INSERT_DEF,DIFF_DEF] >> metis_tac[]
QED

Definition no_self_comunication_def:
  no_self_comunication (Com p _ q _ c)   = (p ≠ q ∧ no_self_comunication c)
∧ no_self_comunication (Sel p _ q c)     = (p ≠ q ∧ no_self_comunication c)
∧ no_self_comunication (IfThen _ _ c c') = (no_self_comunication c ∧
                                            no_self_comunication c')
∧ no_self_comunication (Let _ _ _ _ c)   = no_self_comunication c
∧ no_self_comunication _                 = T
End

Theorem no_freeprocs_eq:
  ∀p1 τ. p1 ∉ freeprocs τ ⇔ (sender τ ≠ SOME p1 ∧ receiver τ ≠ SOME p1)
Proof
  rw [] \\ Cases_on ‘τ’
  \\ fs [sender_def,freeprocs_def,receiver_def]
  \\ rw [] \\ metis_tac []
QED

Theorem freeprocs_eq:
  ∀p1 τ. p1 ∈ freeprocs τ ⇔ (sender τ = SOME p1 ∨ receiver τ = SOME p1)
Proof
  rw [] \\ Cases_on ‘τ’
  \\ fs [sender_def,freeprocs_def,receiver_def]
  \\ rw [] \\ metis_tac []
QED

Theorem send_recv_neq:
  ∀p q τ. p ≠ q
  ∧ sender τ = SOME p
  ∧ receiver τ = SOME q
  ⇒ sender τ ≠ SOME q
Proof
  rw [] \\ CCONTR_TAC \\ fs []
QED

val _ = export_theory ()
