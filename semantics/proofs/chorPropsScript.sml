open preamble choreoUtilsTheory chorSemTheory chorLangTheory chorLangPropsTheory;

val _ = new_theory "chorProps";

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

(* Two list in a lcong relationship have the same length *)
Theorem lcong_length:
  ∀l l'. l τ≅ l' ⇒ LENGTH l = LENGTH l'
Proof
  ho_match_mp_tac lcong_strongind
  \\ rw []
QED

(* An empty list can't be in an lcong relationship with a non empty list *)
Theorem not_nil_lcong_cons:
  ∀h l. ¬ ([] τ≅ h :: l)
Proof
  rw [] >> CCONTR_TAC  >> rw []
  \\ IMP_RES_TAC lcong_length
  \\ fs [LENGTH]
QED

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

(* Applying `lrm` at both sides of an lcong preserves the relation *)
Theorem lcong_lrm:
  ∀e l l'. l τ≅ l' ⇒ lrm l e τ≅ lrm l' e
Proof
  GEN_TAC
  \\ ho_match_mp_tac lcong_strongind
  \\ rw [lcong_rules]
  \\ IMP_RES_TAC lcong_trans
  \\ Cases_on `MEM e (h ++ [t1; t2])`
  >- (`MEM e (h ++ [t2; t1])` by fs [MEM_PERM,PERM_APPEND_IFF,PERM_SWAP_AT_FRONT]
     \\ rw [lrm_mem_append]
     \\ Cases_on `MEM e h`
     \\ rw [lrm_mem_append,lcong_rules,lrm_not_mem_append]
     \\ rw [lrm_def,lcong_rules])
  >- (`¬MEM e (h ++ [t2; t1])` by fs [MEM_PERM,PERM_APPEND_IFF,PERM_SWAP_AT_FRONT]
     \\ rw [lrm_not_mem_append,lcong_rules])
QED

(* [] can only be related in `lcong` with  (itself) [] *)
Theorem lcong_nil_simp:
  ∀l. (l τ≅ [] ⇔ l = []) ∧ ([] τ≅ l ⇔ l = [])
Proof
  Cases_on `l`
  >- rw [lcong_rules]
  >- (fs [] >> metis_tac [not_nil_lcong_cons,lcong_refl])
QED

(* Prepending and element (`h`) preserves `lcong` *)
Theorem lcong_cons:
  ∀h l l'. lcong l l' ⇒ lcong (h :: l) (h :: l')
Proof
  GEN_TAC
  \\ ho_match_mp_tac lcong_strongind
  \\ rw [lcong_rules]
  \\ metis_tac [lcong_rules,GSYM APPEND |> CONJUNCT2]
QED

(* Removing the identical heads preserves `lcong` *)
Theorem cons_lcong:
  ∀h l l'. h :: l τ≅ h :: l' ⇒ l τ≅ l'
Proof
  rw []
  \\ IMP_RES_TAC lcong_lrm
  \\ pop_assum (ASSUME_TAC o Q.SPEC `h`)
  \\ fs [lrm_def]
QED

(* An slightly more specific case of `lcong_lrm` *)
Theorem lcong_cons_simp:
  ∀h l h' l'. h ≠ h' ∧ h :: l τ≅ h' :: l'
   ⇒ l τ≅ h' :: lrm l' h
Proof
  rw []
  \\ IMP_RES_TAC lcong_lrm
  \\ pop_assum (ASSUME_TAC o Q.SPEC `h`)
  \\ rfs [lrm_def]
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

(* In a list of valid actions (`h`) there are no LFix actions *)
Theorem valid_actions_not_lfix:
  ∀t h p v. valid_actions t h ⇒ ¬ MEM LFix h
Proof
  rw []
  \\ CCONTR_TAC
  \\ fs [valid_actions_def,EVERY_MEM]
  \\ RES_TAC
  \\ fs [valid_action_def]
QED

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
  >- local_metis >- local_metis >- local_metis
  >- local_metis >- local_metis >- local_metis
  \\ res_tac
  \\ `z = z'` by (drule trans_state \\ rw [state_from_tag_def])
  \\ rveq \\ qexists_tac `z` \\ local_metis
  end
QED

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
  ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> fs[free_variables_def,defined_vars_def,DIFF_INSERT,
        free_variables_dsubst_eq_Fix] >> rw[]
  >> fs[DELETE_DEF,DIFF_DEF,SUBSET_DEF] >> rpt strip_tac
  >> fs[] >> metis_tac[]
QED

(* Transitions preserve ‘no_undefined_vars’ since they can not remove
   variables from the state
*)
Theorem no_undefined_vars_trans_pres:
  ∀sc alpha sc'. no_undefined_vars sc ∧ trans sc alpha sc' ⇒ no_undefined_vars sc'
Proof
  rpt gen_tac >> disch_then(MAP_EVERY assume_tac o CONJUNCTS)
  >> qpat_x_assum `no_undefined_vars _` mp_tac
  >> qpat_x_assum `trans _ _ _` mp_tac
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`alpha`,`sc'`])
  >> ho_match_mp_tac trans_strongind
  >> rpt strip_tac
  >> imp_res_tac defined_vars_mono
  >> imp_res_tac free_vars_mono
  >> fs[no_undefined_vars_def,free_variables_def,DELETE_SUBSET_INSERT,defined_vars_def,SUBSET_OF_INSERT,
        free_variables_dsubst_eq_Fix]
  >> fs[SUBSET_DEF,INSERT_DEF,DIFF_DEF] >> metis_tac[]
QED

(* Transitions preserve ‘no_undefined_vars’ since they can not remove
   variables from the state
*)
Theorem no_undefined_vars_trans_s_pres:
  ∀sc alpha sc'. no_undefined_vars sc ∧ trans_s sc sc' ⇒ no_undefined_vars sc'
Proof
  rpt gen_tac \\ disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS)
  \\ rpt (pop_assum mp_tac) \\ simp[trans_s_def]
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [`sc`,`sc'`])
  \\ ho_match_mp_tac RTC_INDUCT \\ rw[]
  \\ metis_tac [no_undefined_vars_trans_pres]
QED

(* A tag does not remove variables from the state, hence preserving
   ‘no_undefined_vars_def’
*)
Theorem no_undefined_vars_from_tags:
  ∀c s α.
   no_undefined_vars (s,c) ⇒ no_undefined_vars (state_from_tag s α, c)
Proof
  rw [no_undefined_vars_def,free_variables_def]
  \\ Cases_on `α` \\ fs [state_from_tag_def]
  \\ ho_match_mp_tac SUBSET_TRANS
  \\ metis_tac [SUBSET_OF_INSERT]
QED

(* Transitions preserve ‘no_self_comunication’ since they change
   the shape of the choreography aside from consuming its operations
*)
Theorem no_self_comunication_trans_pres:
  ∀s c τ l s' c'.
   no_self_comunication c ∧ trans (s,c) (τ,l) (s',c')
   ⇒ no_self_comunication c'
Proof
  rpt gen_tac \\ disch_then(MAP_EVERY assume_tac o CONJUNCTS)
  \\ qpat_x_assum `no_self_comunication _` mp_tac
  \\ qpat_x_assum `trans _ _ _` mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘s’,‘c’,‘τ’,‘l’,‘s'’,‘c'’])
  \\ ho_match_mp_tac trans_pairind
  \\ rw [no_self_comunication_def,
         no_self_comunication_dsubst]
QED

(* Check if a tag matches the head of a choreography *)
Definition chor_match_def:
  chor_match (LCom p v q x)  (Com p' v' q' x' c)  = ((p,v,q,x)  = (p',v',q',x'))
∧ chor_match (LSel p b q)    (Sel p' b' q' c)     = ((p,b,q)  = (p',b',q'))
∧ chor_match (LLet v p f l)  (Let v' p' f' l' c)  = ((v,p,f,l) = (v',p',f',l'))
∧ chor_match (LTau p v)      (IfThen v' p' c1 c2) = ((p,v)     = (p',v'))
∧ chor_match  LFix           (Fix _ _)            = T
∧ chor_match  _              _                    = F
End

(* Generates the corresponding tag that would consume
   the front of the choreography
*)
Definition chor_tag_def:
  chor_tag (Com p v q x _)  = LCom p v q x
∧ chor_tag (Sel p b q _)    = LSel p b q
∧ chor_tag (Let v p f l _)  = LLet v p f l
∧ chor_tag (IfThen v p _ _) = LTau p v
∧ chor_tag (Fix _ _)        = LFix
End


(* Drops the head of the choreography updating the state in the process.
   Its equivalent to one synchronous step in the semantics.
*)
Definition chor_tl_def:
  chor_tl s Nil             = (s,Nil)
∧ chor_tl s (Call v)        = (s,Call v)
∧ chor_tl s (Fix dn c)      = (s,dsubst c dn (Fix dn c))
∧ chor_tl s (Com p v q x c) = (s |+ ((x,q),(THE o FLOOKUP s) (v,p)),c)
∧ chor_tl s (Sel p b q c)   = (s,c)
∧ chor_tl s (Let v p f l c) =
    (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) l))),c)
∧ chor_tl s (IfThen v p c1 c2) =
    (if FLOOKUP s (v,p) = SOME [1w] then (s,c1)
     else if ∃w. FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w] then (s,c2)
     else (s,IfThen v p c1 c2))
End

(* Advances the choreography until the given tag
   matches removing everything in its path
   (state is still updated)
*)
Definition syncTrm_def:
  syncTrm (k:num) (s,Nil) τ              = NONE
∧ syncTrm  k      (s,Call v) τ           = NONE
∧ syncTrm  k      (s,IfThen v p c1 c2) τ =
   (if (k = 0) then NONE
    else if chor_match τ (IfThen v p c1 c2)
         then SOME (chor_tl s (IfThen v p c1 c2))
         else if FLOOKUP s (v,p) = SOME [1w]
              then syncTrm (k-1) (s,c1) τ
              else if ∃w. FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w]
                   then syncTrm (k-1)(s,c2) τ
                   else NONE)
∧ syncTrm k (s,c) τ =
   (if (k = 0) then NONE
    else if chor_match τ c
         then SOME (chor_tl s c)
         else syncTrm (k-1) (chor_tl s c) τ)
End

(* Alternative induction principle *)
Theorem syncTrm_pairind =
  syncTrm_ind
  |> Q.SPEC ‘λk (s,c) τ. P k s c τ’
  |> SIMP_RULE std_ss [FORALL_PROD]
  |> Q.GEN ‘P’

Definition not_finish_def[simp]:
  not_finish c = (c ≠ Nil ∧ ∀x. c ≠ Call x)
End

(* A choreography can always advance synchronously consuming
   the operation at the front
*)
Theorem chor_tag_trans:
  ∀s c k p.
   no_undefined_vars (s,c)
   ∧ not_finish c
   ∧ no_self_comunication c
   ∧ syncTrm k (s,c) (chor_tag c) = SOME p
   ⇒ trans (s,c) (chor_tag c,[]) p
Proof
  rw [] \\ Cases_on ‘c’
  \\ fs [ chor_tag_def,syncTrm_def,chor_match_def
        , chor_tl_def,no_self_comunication_def]
  \\ rveq
  >- (IF_CASES_TAC
      >- fs [trans_if_true]
      \\ drule no_undefined_FLOOKUP_if \\ rw [] \\ fs []
      \\ fs [trans_if_false])
  >- (drule no_undefined_FLOOKUP_com \\ rw []
     \\  fs [trans_com])
  >- (drule no_undefined_FLOOKUP_let \\ rw []
     \\  fs [trans_let])
  \\ fs [trans_sel,trans_fix]
QED

(* ‘syncTrm’ preserves does not remove any variable from the state *)
Theorem no_undefined_syncTrm:
  ∀k s c τ p.
    no_undefined_vars (s,c) ∧ syncTrm k (s,c) τ = SOME p
    ⇒ no_undefined_vars p
Proof
  ho_match_mp_tac syncTrm_pairind
  \\ rw [syncTrm_def,chor_tl_def,
         no_undefined_vars_def,
         free_variables_def,
         free_variables_dsubst_eq_Fix,
         DELETE_SUBSET_INSERT]
QED

(* ‘syncTrm’ does not add self communicating operation into the choreography *)
Theorem no_self_comunication_syncTrm:
  ∀k s c τ q r. no_self_comunication c ∧ syncTrm k (s,c) τ = SOME (q,r) ⇒ no_self_comunication r
Proof
  ho_match_mp_tac syncTrm_pairind
  \\ rw [syncTrm_def,chor_tl_def,
         free_variables_dsubst_eq_Fix,
         no_self_comunication_dsubst,
         no_self_comunication_def]
  \\ rw [no_self_comunication_def]
QED

(* Basic RTC rules (reflexivity) *)
Theorem trans_sync_refl:
  ∀p. trans_sync p p
Proof
  rw [trans_sync_def,RTC_RULES]
QED

(* Basic RTC rules (single step) *)
Theorem trans_sync_step:
  ∀p p' τ q. trans p (τ,[]) p' ∧ trans_sync p' q ⇒ trans_sync p q
Proof
  rw [trans_sync_def] \\ ho_match_mp_tac RTC_TRANS
  \\ qexists_tac ‘p'’ \\ rw []
  \\ asm_exists_tac \\ fs []
QED

(* Basic RTC rules (transitivity) *)
Theorem trans_sync_trans:
  ∀p p' q. trans_sync p p' ∧ trans_sync p' q ⇒ trans_sync p q
Proof
  metis_tac [trans_sync_def,RTC_RTC]
QED

(* Basic RTC rules (id) *)
Theorem trans_sync_one:
  ∀p τ q. trans p (τ,[]) q ⇒ trans_sync p q
Proof
  rw [trans_sync_def] \\ ho_match_mp_tac RTC_SINGLE
  \\ asm_exists_tac \\ fs []
QED

(* One can synchronously consume as much of a choreography
   as needed to perform any tag operation. If the tag
   does not match anything in the choreography we just
   consume the whole thing.
*)
Theorem Trm_trans:
  ∀s c τ k p.
   no_undefined_vars (s,c) ∧
   no_self_comunication c ∧
   syncTrm k (s,c) τ = SOME p
   ⇒ trans_sync (s,c) p
Proof
  rw []
  \\ drule chor_tag_trans \\ rw []
  \\ rpt (first_x_assum mp_tac)
  \\ MAP_EVERY Q.SPEC_TAC [(‘p’,‘p’),(‘τ’,‘τ’),(‘c’,‘c’),(‘s’,‘s’),(‘k’,‘k’)]
  \\ ho_match_mp_tac syncTrm_pairind
  \\ rw [ no_self_comunication_def
        , no_self_comunication_dsubst
        , free_variables_dsubst_eq_Fix
        , no_undefined_vars_def
        , syncTrm_def
        , chor_match_def
        , chor_tl_def
        , free_variables_def
        , trans_sync_one
        , trans_sync_refl
        , chor_tag_def]
  \\ first_x_assum (qspec_then ‘k’ assume_tac) \\ rfs []
  \\ TRY (ho_match_mp_tac trans_sync_one \\ asm_exists_tac \\ fs [])
  \\ ho_match_mp_tac trans_sync_step \\ asm_exists_tac \\ fs []
  \\ first_x_assum irule \\ rw []
  \\ TRY (irule chor_tag_trans)
  \\ fs [no_undefined_vars_def,DELETE_SUBSET_INSERT]
  \\ rw [no_self_comunication_dsubst
         , no_self_comunication_def
         , free_variables_dsubst_eq_Fix]
  \\ asm_exists_tac \\ fs []
QED

Definition variables_def:
  (variables (chorLang$Nil) = {}) /\
  (variables (Call x) = {}) /\
  (variables (Fix x c) = variables c) /\
  (variables (IfThen v p c1 c2) = {(v,p)} ∪ (variables c1 ∪ variables c2)) /\
  (variables (Com p1 v1 p2 v2 c) = {(v1,p1);(v2,p2)} ∪ (variables c)) /\
  (variables (Let v p f vl c) = set(MAP (λv. (v,p)) vl) ∪ {(v,p)} ∪ variables c) /\
  (variables (Sel p b q c) = variables c)
End

Theorem dsubst_subset_variables:
  ∀c c' dn.
    variables (dsubst c dn c') ⊆ variables c ∪ variables c'
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [variables_def,dsubst_def]
  \\ fs [variables_def,dsubst_def]
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF])
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac []
QED

Theorem variables_subset_dsubst:
  ∀c c' dn.
    variables c ⊆ variables (dsubst c dn c')
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [variables_def,dsubst_def]
  \\ fs [SUBSET_DEF]
QED

Theorem variables_dsubst_eq:
  ∀c dn. variables (dsubst c dn c) = variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [variables_subset_dsubst,
                dsubst_subset_variables,
                UNION_IDEMPOT]
QED

Theorem variables_dsubst_eq_Fix:
  ∀c x y. variables (dsubst c x (Fix y c)) = variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [variables_subset_dsubst,
                dsubst_subset_variables,
                variables_def,
                UNION_IDEMPOT]
QED

Theorem trans_variables_mono:
  ∀s c a l s' c'.
  trans (s,c) (a,l) (s',c') ⇒
  variables c' ⊆ variables c
Proof
  ho_match_mp_tac trans_pairind >>
  rw[variables_def,variables_dsubst_eq_Fix] >>
  fs[SUBSET_DEF]
QED

Theorem trans_s_variables_mono:
  ∀s c s' c'.
  trans_s (s,c) (s',c') ⇒
  variables c' ⊆ variables c
Proof
  rpt strip_tac >>
  ‘(∀sc sc'. (λp q. ∃s. chorSem$trans p s q) sc sc' ⇒ combin$C pred_set$SUBSET ((λ(s,c). variables c) sc) ((λ(s,c). variables c) sc'))’
    by(Cases >> Cases >> rw[] >> rename1 ‘trans _ a _’ >> Cases_on ‘a’ >> metis_tac[trans_variables_mono]) >>
  dxrule RTC_lifts_reflexive_transitive_relations >>
  disch_then(qspecl_then [‘(s,c)’,‘(s',c')’] mp_tac) >>
  simp[] >>
  disch_then match_mp_tac >>
  fs[trans_s_def] >>
  fs[reflexive_def,transitive_def] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem free_variables_variables:
  free_variables c ⊆ variables c
Proof
  Induct_on ‘c’ >> rw[free_variables_def,variables_def] >> fs[SUBSET_DEF] >> rw[] >> res_tac
QED

val _ = export_theory ()
