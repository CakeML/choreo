open preamble

open chorSemTheory chorPropsTheory chorCongSemTheory chorLangTheory

val _ = new_theory "congProof";

(* chorSem$label to chorCongSem$label conversion *)
Definition toCong_def:
  toCong (LTau p v)      = LTau p NONE
∧ toCong (LCom p v q v') = LCom p v q v'
∧ toCong (LSel p b q)    = LSel p b q
∧ toCong (LLet v p f vl) = LTau p (SOME v)
End

(* `chorTrm s τ c` removes the sub-expression denoted by `τ` in `c`
   under state `s` (the state is only used for If expressions)
*)
Definition chorTrm_def:
  chorTrm (k:num) s (LCom p v q x) (Com p' v' q' x' c) =
    (if (p,v,q,x) = (p',v',q',x') then SOME c
     else OPTION_MAP (Com p' v' q' x') (chorTrm k s (LCom p v q x) c))
∧ chorTrm k s (LSel p b q) (Sel p' b' q' c) =
    (if (p,b,q) = (p',b',q') then SOME c
     else OPTION_MAP (Sel p' b' q') (chorTrm k s (LSel p b q) c))
∧ chorTrm k s (LLet v p f vl) (Let v' p' f' vl' c) =
    (if (v,p,f,vl) = (v',p',f',vl') then SOME c
     else OPTION_MAP (Let v' p' f' vl') (chorTrm k s (LLet v p f vl) c))
∧ chorTrm k s (LTau p v) (IfThen v' p' c1 c2) =
    (if (p,v) = (p',v')
     then if FLOOKUP s (v,p) = SOME [1w] then SOME c1
          else if ∃w. FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w] then SOME c2
          else SOME (IfThen v' p' c1 c2) (* Imposible? *)
     else  OPTION_MAP2 (IfThen v' p') (chorTrm k s (LTau p v) c1) (chorTrm k s (LTau p v) c2))
∧ chorTrm k s LFix (Fix x c)         = SOME c
∧ chorTrm k s τ (Fix x c)            = (if k = 0 then NONE
                                        else chorTrm (k-1) s τ (dsubst c x (Fix x c)))
∧ chorTrm k s τ (Com p' v' q' x' c)  = OPTION_MAP  (Com p' v' q' x')  (chorTrm k s τ c)
∧ chorTrm k s τ (Sel p' b' q' c)     = OPTION_MAP  (Sel p' b' q')     (chorTrm k s τ c)
∧ chorTrm k s τ (Let v' p' f' vl' c) = OPTION_MAP  (Let v' p' f' vl') (chorTrm k s τ c)
∧ chorTrm k s τ (IfThen v' p' c1 c2) = OPTION_MAP2 (IfThen v' p')     (chorTrm k s τ c1)
                                                                      (chorTrm k s τ c2)
∧ chorTrm k s τ (Call x)             = NONE
∧ chorTrm k s τ Nil                  = NONE
Termination
  WF_REL_TAC ‘inv_image (measure I LEX
                         measure chor_size)
                        (λ(k,s,τ,c). (k,c))’
  \\ rpt strip_tac
End

Theorem chorTrm_k_scong:
  ∀k s τ c0 c c' k'.
    chorTrm k s τ c0 = SOME c  ∧
    chorTrm k' s τ c0 = SOME c'
    ⇒ c ≅ c'
Proof
  ho_match_mp_tac chorTrm_ind
  \\ rw [chorTrm_def]
  \\ metis_tac [scong_rules]
QED

Theorem chorTrm_IS_SOME:
  ∀k s τ c k'.
    k < k' ∧ IS_SOME (chorTrm k s τ c)
    ⇒ IS_SOME (chorTrm k' s τ c)
Proof
  ho_match_mp_tac chorTrm_ind
  \\ rw [chorTrm_def]
  \\ TRY (qpat_x_assum ‘_ ⇒ _ ’ mp_tac
         \\ impl_tac >- fs []
         \\ disch_then drule
         \\ strip_tac
         \\ qmatch_goalsub_abbrev_tac ‘IS_SOME (_ _ t0)’
         \\ Cases_on ‘t0’ \\ fs [] \\ simp [] \\ NO_TAC)
  \\ TRY (qpat_x_assum ‘_ ⇒ _ ’ mp_tac
          \\ impl_tac >- fs []
          \\ disch_then drule
          \\ strip_tac
          \\ qpat_x_assum ‘_ ⇒ ∀k''. _ ’ mp_tac
          \\ impl_tac >- fs []
          \\ disch_then drule
          \\ strip_tac
          \\ qmatch_asmsub_abbrev_tac ‘IS_SOME (OPTION_MAP2 _ t0 t1)’
          \\ MAP_EVERY Cases_on [‘t0’,‘t1’] \\ fs [] \\ simp []
          \\ qmatch_goalsub_abbrev_tac ‘IS_SOME (OPTION_MAP2 _ t2 t3)’
          \\ MAP_EVERY Cases_on [‘t2’,‘t3’] \\ fs [] \\ simp []
          \\ NO_TAC)
  \\ TRY (first_x_assum drule \\ strip_tac
          \\ qmatch_asmsub_abbrev_tac ‘IS_SOME (OPTION_MAP _ t0)’
          \\ Cases_on ‘t0’ \\ fs [] \\ simp []
          \\ qmatch_goalsub_abbrev_tac ‘IS_SOME (OPTION_MAP _ t1)’
          \\ Cases_on ‘t1’ \\ fs [] \\ simp []
          \\ NO_TAC)
  \\ first_x_assum drule
  \\ first_x_assum drule
  \\ strip_tac \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac ‘IS_SOME (OPTION_MAP2 _ t0 t1)’
  \\ MAP_EVERY Cases_on [‘t0’,‘t1’] \\ fs [] \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘IS_SOME (OPTION_MAP2 _ t2 t3)’
  \\ MAP_EVERY Cases_on [‘t2’,‘t3’] \\ fs [] \\ simp []
QED

Theorem chorTrm_IS_NONE:
  ∀k s τ c k'.
    k' < k ∧ IS_NONE (chorTrm k s τ c)
    ⇒ IS_NONE (chorTrm k' s τ c)
Proof
  ho_match_mp_tac chorTrm_ind
  \\ rw [chorTrm_def]
  \\ TRY (qpat_x_assum ‘_ ⇒ _ ’ mp_tac
         \\ impl_tac >- fs []
         \\ disch_then drule
         \\ strip_tac
         \\ fs [] \\ simp [] \\ NO_TAC)
  \\ TRY (Cases_on ‘k = 0’ \\ fs []
          \\ CCONTR_TAC
          \\ ‘k' - 1 < k - 1’ by fs []
          \\ first_x_assum drule
          \\ fs []
          \\ CCONTR_TAC \\ fs []
          \\ NO_TAC)
QED

(* The application of `chorTrm` preserves `scong` *)
Theorem chorTrm_scong:
  ∀s τ c c'. c ≅ c' ⇒ chorTrm s τ c ≅ chorTrm s τ c'
Proof
  rpt GEN_TAC
  \\ `∀c c'.
        c ≅ c'
        ⇒ c ≅ c'
        ⇒ chorTrm s τ c ≅ chorTrm s τ c'`
     suffices_by (metis_tac [])
  \\ Cases_on `τ`
  \\ ho_match_mp_tac scong_strongind
  \\ rw [chorTrm_def]
  \\ rfs [scong_rules]
  \\ IMP_RES_TAC scong_trans
QED

(* The effect of any valid transition `trans (s,c) (τ,l) (s',c')` over
   the (start/ing) choreograpy `c` is the resulting (result/ing)
   choreography `c'` that must be equal to the removal of the
   sub-expression denoted by `τ` in `c` (Effectively `lrm s τ c`).

   This is specially relevant since from this result and
   `chorTrm_scong` we can show the congruence of the resulting
   choreographies of a pair of transitions (both using label `τ` and
   starting state `s` ) from the congruence of their starting
   choreographies


     c1 ≅ c2 ∧ trans (s,c1) (τ,l) (s',c1') ∧ trans (s,c2) (τ,l') (s',c2')
    ----------------------------------------------------------------------
                             c1' ≅ c2'
*)
Theorem trans_imp_chorTrm:
   ∀s c τ l s' c'.
    trans (s,c) (τ,l) (s',c')
    ⇒ c' = chorTrm s τ c
Proof
  rpt GEN_TAC
  \\ `∀s c τ' l s' c'.
       trans (s,c) (τ',l) (s',c')
       ⇒ trans (s,c) (τ',l) (s',c')
       ∧ τ' = τ
       ⇒ c' = chorTrm s τ c`
     suffices_by (metis_tac [])
  \\ Cases_on `τ`
  \\ ho_match_mp_tac trans_pairind
  \\ rw [chorTrm_def,trans_rules]
  \\ rfs [trans_rules,chorSemTheory.freeprocs_def]
  \\ metis_tac []
QED

(* An streamlined version of `trans_imp_chorTrm` *)
Theorem trans_chorTrm_eq:
   ∀s c τ l s' c'.
    trans (s,c) (τ,l) (s',c') ⇒ trans (s,c) (τ,l) (s',chorTrm s τ c)
Proof
 rw []
 \\ first_assum ASSUME_TAC
 \\ IMP_RES_TAC trans_imp_chorTrm
 \\ rw []
QED

(* If two (starting) choreographies (`c1`,`c1'`) are congruent then a
   transition with label `τ` and async actions list `l` from any of
   them will imply there exists a transition from the opposite
   choreography with the same label `τ` and a list `l`
                                       ________________________
        trans (s,c1)  (τ,l)  (s',c2)  |                        |
  c1-------------------------------------c2  = chorTrm s τ c1  |
   |                                  |  |         |           |
   ≅                                  |  ≅         ≅           |
   |    trans (s,c1') (τ,l)  (s',c2') |  |         |           |
  c1'------------------------------------c2' = chorTrm s τ c1' |
                                      |________________________|*

   * This is not actually in the theorem but can be easily obtained
     using `trans_imp_chorTrm` and `chorTrm_scong`

*)
Theorem trans_from_cong:
    ∀c1 c1'.
    c1 ≅ c1'
    ⇒ (∀s s' τ c2 c2' l l'.
        (trans (s,c1)  (τ,l)  (s',c2)
         ⇒ ∃l' c2'. trans (s,c1') (τ,l') (s',c2') ∧ l τ≅ l')
        ∧
        (trans (s,c1') (τ,l') (s',c2')
               ⇒ ∃l c2. trans (s,c1) (τ,l) (s',c2) ∧ l' τ≅ l))
Proof
  let val cases_last  = rpt (qpat_x_assum `trans _ _ _` mp_tac)
                        \\ disch_then (ASSUME_TAC o SIMP_RULE std_ss [Once trans_cases])
                        \\ rw [] >> rfs [] >> rw []
      val cases_goal  = rw [Once trans_cases, chorSemTheory.freeprocs_def]
                           \\ fs [chorSemTheory.freeprocs_def]
      val super_metis = metis_tac [trans_rules, lcong_rules]
      val check_trans   = qpat_assum `trans _ _ _` (K ALL_TAC)
      val list_of_trans = [`trans (_, Com _ _ _ _ _) _ _`
                          ,`trans (_, Sel _ _ _ _) _ _`
                          ,`trans (_, Let _ _ _ _ _) _ _`
                          ,`trans (_, IfThen _ _ _ _) _ _`]
      val check_forall = qpat_assum `∀s s' τ. (∃l c2. trans _ _ _)
                                                ⇔ ∃l' c2. trans _ _ _` (K ALL_TAC)
      val check_lcong = qpat_assum `_ τ≅ _` (K ALL_TAC)
      val check_chor  = FIRST (map (fn q => qpat_assum q (K ALL_TAC)) list_of_trans)
      val lcong_if    = IMP_RES_TAC lcong_refl
                        \\ IMP_RES_TAC lcong_trans
                        \\ IMP_RES_TAC trans_if_swap
      val lcong_if_com = IMP_RES_TAC lcong_cons
                         \\ IMP_RES_TAC cons_lcong
                         \\ metis_tac [trans_rules]
      val l_tac_gen = fn lcong_tac =>
                         (check_chor >> cases_last)
                           ORELSE check_forall
                           ORELSE (check_lcong >> lcong_tac >> super_metis)
                           ORELSE (cases_goal >> super_metis)
                           ORELSE super_metis
      val l_tac = l_tac_gen (FAIL_TAC "Nope")
      val l_if_tac = l_tac_gen lcong_if
      val l_if_com_tac = l_tac_gen lcong_if_com
      val rpt_l_tac = rpt l_tac
      val rpt_l_tac_if =  rpt l_if_tac
      val rpt_l_tac_if_com = rpt l_if_com_tac
      val rptn = fn tac => fn n => List.tabulate (n,K tac)
      val tac =
       fn (t1,t2,l) =>
          l_tac >> l_tac >- l_tac >- l_tac >- l_tac >- l_tac >- l_tac
          >- (Q.EXISTS_TAC `^t2::^t1::^l`
             \\ CONV_TAC (ONCE_DEPTH_CONV EXISTS_AND_REORDER_CONV)
             \\ rw [] >- (sg `DISJOINT (chorSem$freeprocs ^t1)
                                       (chorSem$freeprocs ^t2)`
                         >- rw [chorSemTheory.freeprocs_def]
                         >- rw [lcong_reord |> Q.SPEC `[]`
                                            |> SIMP_RULE std_ss [APPEND]])
           >- l_tac)
  in
  (ho_match_mp_tac scong_ind
  \\ rw []
  \\ TRY (`p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4`
          by (fs [INTER_DEF,EMPTY_DEF,FUN_EQ_THM] >> metis_tac [])))
  >- super_metis >- super_metis >- super_metis
  >- super_metis >- super_metis >- super_metis
  >- tac (``chorSem$LCom p1 v1 p2 v2``
         ,``chorSem$LCom p3 v3 p4 v4``
         ,``l : chorSem$label list``)
  >- tac (``chorSem$LCom p3 v3 p4 v4``
         ,``chorSem$LCom p1 v1 p2 v2``
         ,``l' : chorSem$label list``)
  >- tac (``chorSem$LCom p1 v1 p2 v2``
         ,``chorSem$LSel p3 v3 p4``
         ,``l : chorSem$label list``)
  >- tac (``chorSem$LSel p3 v3 p4``
         ,``chorSem$LCom p1 v1 p2 v2``
         ,``l' : chorSem$label list``)
  >- tac (``chorSem$LSel p1 v1 p2``
         ,``chorSem$LSel p3 v3 p4``
         ,``l : chorSem$label list``)
  >- tac (``chorSem$LSel p3 v3 p4``
         ,``chorSem$LSel p1 v1 p2``
         ,``l' : chorSem$label list``)
  >- rpt_l_tac >- rpt_l_tac >- rpt_l_tac
  >- rpt_l_tac >- rpt_l_tac >- rpt_l_tac
  >- (l_tac >> l_tac >> l_tac
     >- l_tac >- l_tac >- l_tac
     >- l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `l` >> rw [lcong_sym] >> l_if_tac))
  >- (l_tac >> l_tac >> l_tac
     >- l_tac >- l_tac >- l_tac
     >- l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `l'` >> rw [lcong_sym] >> l_if_tac))
  >- (l_tac >> l_tac >- l_tac >- l_tac >- l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `LCom p1 v1 p2 v2 :: l'` >> rw [lcong_sym] >> l_if_com_tac))
  >- (l_tac >> l_tac >> l_tac >- l_tac >- l_tac >- l_tac >- l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `LCom p1 v1 p2 v2 :: l` >> rw [lcong_sym] >> l_if_com_tac))
  >- (l_tac >> l_tac >- l_tac >- l_tac >- l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `LSel p1 b p2 :: l'` >> rw [lcong_sym] >> l_if_com_tac))
  >- (l_tac >> l_tac >> l_tac >- l_tac >- l_tac >- l_tac >- l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `LSel p1 b p2 :: l` >> rw [lcong_sym] >> l_if_com_tac))
  >- (l_tac >> l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `l` >> rw [lcong_sym] >> l_if_tac))
  >- (l_tac >> l_tac >> l_tac >- l_tac >- l_tac >- l_tac
     >- (Q.EXISTS_TAC `l'` >> rw [lcong_sym] >> l_if_tac))
  >- (l_tac >- l_tac >- l_tac
     >- (RES_TAC >> Q.EXISTS_TAC `l'''` >> rw [lcong_sym] >> l_if_tac))
  >- (l_tac >- l_tac >- l_tac
     >- (RES_TAC >> Q.EXISTS_TAC `l'''` >> rw [lcong_sym] >> l_if_tac))
  >- rpt_l_tac >- rpt_l_tac
  >- (l_tac >- l_tac >- l_tac
     >- (RES_TAC >> IMP_RES_TAC lcong_cons >> l_if_tac))
  >- (l_tac >- l_tac >- l_tac
     >- (RES_TAC >> IMP_RES_TAC lcong_cons >> l_if_tac))
  >- (l_tac >- l_tac >- l_tac
     >- (RES_TAC >> IMP_RES_TAC lcong_cons >> l_if_tac))
  >- (l_tac >- l_tac >- l_tac
     >- (RES_TAC >> IMP_RES_TAC lcong_cons >> l_if_tac))
  end
QED

(* A more human readable versin of `trans_from_cong` *)
Theorem trans_from_cong':
   ∀c1 c1' s s' τ.
    c1 ≅ c1'
    ⇒ (∃l  c2. trans (s ,c1 ) (τ,l ) (s',c2 ))
     = ∃l' c2'. trans (s,c1') (τ,l') (s',c2')
Proof
  rw [] >> EQ_TAC >> rw []
  \\ IMP_RES_TAC trans_from_cong
  \\ metis_tac []
QED

(* Equality of chorSem$freeprocs and chorTrm$freeprocs *)
Theorem freeprocs_eq:
  ∀τ. freeprocs τ = freeprocs (toCong τ)
Proof
  Cases_on `τ`
  >> rw [freeprocs_def,chorSemTheory.freeprocs_def,toCong_def]
QED

(* Equality of chorSem$written and chorTrm$written *)
Theorem written_eq:
  ∀τ. written τ = written (toCong τ)
Proof
  Cases_on `τ`
  >> rw [written_def,chorSemTheory.written_def,toCong_def]
QED

(* `transCong` implies `trans` up to `≅` on the resulting choreography *)
Theorem transCong_imp_trans:
   ∀c s τ c' s'.
    transCong (s,c) τ (s',c')
    ⇒ ∃l τ' c''. c' ≅ c'' ∧ trans (s,c) (τ',l) (s',c'') ∧ toCong τ' = τ
Proof
  rpt GEN_TAC
  \\ `∀s c τ s' c'.
       transCong (s,c) τ (s',c')
        ⇒ ∃l τ' c''. c' ≅ c'' ∧ trans (s,c) (τ',l) (s',c'') ∧ toCong τ' = τ`
     suffices_by (metis_tac [])
  \\ ho_match_mp_tac transCong_pairind
  \\ rw [toCong_def]
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LCom p1 v1 p2 v2`,`c'`])
     \\ rw [scong_rules,trans_rules,toCong_def])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LSel p1 b p2`,`c'`])
     \\ rw [scong_rules,trans_rules,toCong_def])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LLet v p f vl`,`c'`])
     \\ rw [scong_rules,trans_rules,toCong_def])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LTau p v`,`c'`])
     \\ rw [scong_rules,trans_rules,toCong_def])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LTau p v`,`c'`])
     \\ rw [scong_rules,trans_rules,toCong_def])
  >- (rfs []
     \\ EVERY (map Q.EXISTS_TAC [`LCom p1 v1 p2 v2 :: l`,`τ'`,`Com p1 v1 p2 v2 c''`])
     \\ rw [scong_rules]
     \\ `p1 ∈ freeprocs τ'` by rw [freeprocs_eq]
     \\ `p2 ∉ freeprocs τ'` by rw [freeprocs_eq]
     \\ `written τ' ≠ SOME (v1,p1)` by rw [written_eq]
     \\ rw [trans_rules])
  >- (rfs []
     \\ EVERY (map Q.EXISTS_TAC [`LSel p1 b p2 :: l`,`τ'`,`Sel p1 b p2 c''`])
     \\ rw [scong_rules]
     \\ `p1 ∈ freeprocs τ'` by rw [freeprocs_eq]
     \\ `p2 ∉ freeprocs τ'` by rw [freeprocs_eq]
     \\ rw [trans_rules])
  >- (rfs []
     \\ last_assum (ASSUME_TAC o MATCH_MP trans_from_cong)
     \\ RES_TAC
     \\ EVERY (map Q.EXISTS_TAC [`l'`,`τ'`,`c2`])
     \\ rw []
     \\IMP_RES_TAC scong_refl
     \\ IMP_RES_TAC scong_trans
     \\ IMP_RES_TAC trans_imp_chorTrm
     \\ rw []
     \\ match_mp_tac scong_trans
     \\ Q.EXISTS_TAC `chorTrm s τ' c''`
     \\ rw [chorTrm_scong])
QED

val _ = export_theory()
