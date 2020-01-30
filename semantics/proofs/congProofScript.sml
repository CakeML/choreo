open preamble

open semBakeryTheory semCongBakeryTheory astBakeryTheory

val _ = new_theory "congProof";

(* semBakery$label to semCongBakery$label conversion *)
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
  chorTrm s (LCom p v q x) (Com p' v' q' x' c) =
    (if (p,v,q,x) = (p',v',q',x') then c
     else Com p' v' q' x' (chorTrm s (LCom p v q x) c))
∧ chorTrm s (LSel p b q) (Sel p' b' q' c) =
    (if (p,b,q) = (p',b',q') then c
     else Sel p' b' q' (chorTrm s (LSel p b q) c))
∧ chorTrm s (LLet v p f vl) (Let v' p' f' vl' c) =
    (if (v,p,f,vl) = (v',p',f',vl') then c
     else Let v' p' f' vl' (chorTrm s (LLet v p f vl) c))
∧ chorTrm s (LTau p v) (IfThen v' p' c1 c2) =
    (if (p,v) = (p',v')
     then if FLOOKUP s (v,p) = SOME [1w] then c1
          else if ∃w. FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w] then c2
          else IfThen v' p' c1 c2 (* Imposible? *)
     else IfThen v' p' (chorTrm s (LTau p v) c1) (chorTrm s (LTau p v) c2))
∧ chorTrm s τ (Com p' v' q' x' c)  = Com p' v' q' x' (chorTrm s τ c)
∧ chorTrm s τ (Sel p' b' q' c)     = Sel p' b' q' (chorTrm s τ c)
∧ chorTrm s τ (Let v' p' f' vl' c) = Let v' p' f' vl' (chorTrm s τ c)
∧ chorTrm s τ (IfThen v' p' c1 c2) = IfThen v' p' (chorTrm s τ c1) (chorTrm s τ c2)
∧ chorTrm s τ Nil                  = Nil
End

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
  \\ rfs [trans_rules,semBakeryTheory.freeprocs_def]
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
    ⇒ (∀s s' τ c2 c2' l.
        (trans (s,c1)  (τ,l)  (s',c2)
         ⇒ ∃c2'. trans (s,c1') (τ,l) (s',c2'))
        ∧
        (trans (s,c1') (τ,l) (s',c2')
         ⇒ ∃c2. trans (s,c1) (τ,l) (s',c2)))
Proof
  let val cases_last  = rpt (qpat_x_assum `trans _ _ _` mp_tac)
                        \\ disch_then (ASSUME_TAC o SIMP_RULE std_ss [Once trans_cases])
                        \\ rw [] >> rfs [] >> rw []
      val cases_goal  = rw [ Once trans_cases
                           , semBakeryTheory.freeprocs_def
                           , semBakeryTheory.sender_def
                           , semBakeryTheory.receiver_def]
                        \\ fs [ semBakeryTheory.freeprocs_def
                              , semBakeryTheory.sender_def
                              , semBakeryTheory.receiver_def
                              , no_freeprocs_eq]
      val super_metis = metis_tac [trans_rules,send_recv_neq]
      val check_trans   = qpat_assum `trans _ _ _` (K ALL_TAC)
      val list_of_trans = [`trans (_, Com _ _ _ _ _) _ _`
                          ,`trans (_, Sel _ _ _ _) _ _`
                          ,`trans (_, Let _ _ _ _ _) _ _`
                          ,`trans (_, IfThen _ _ _ _) _ _`]
      val check_forall = qpat_assum `∀s s' τ. (∃c2. trans _ _ _)
                                                ⇔ ∃c2. trans _ _ _` (K ALL_TAC)
      val check_chor  = FIRST (map (fn q => qpat_assum q (K ALL_TAC)) list_of_trans)
      val l_tac    = (check_chor >> cases_last)
                      ORELSE check_forall
                      ORELSE (cases_goal >> super_metis)
                      ORELSE super_metis
      val rpt_l_tac = rpt l_tac
  in
  (ho_match_mp_tac scong_ind
  \\ rw []
  \\ TRY (`p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4`
          by (fs [INTER_DEF,EMPTY_DEF,FUN_EQ_THM] >> metis_tac [])))
  >- super_metis >- super_metis >- super_metis
  >- super_metis >- super_metis >- super_metis
  \\ rpt_l_tac
  end
QED

(* A more human readable versin of `trans_from_cong` *)
Theorem trans_from_cong':
   ∀c1 c1' s s' τ l.
    c1 ≅ c1'
    ⇒ (∃c2. trans (s ,c1 ) (τ,l) (s',c2 ))
     = ∃c2'. trans (s,c1') (τ,l) (s',c2')
Proof
  rw [] >> EQ_TAC >> rw []
  \\ IMP_RES_TAC trans_from_cong
  \\ metis_tac []
QED

(* Equality of semBakery$freeprocs and semCongBakery$freeprocs *)
Theorem freeprocs_eq:
  ∀τ. freeprocs τ = freeprocs (toCong τ)
Proof
  Cases_on `τ`
  >> rw [freeprocs_def,semBakeryTheory.freeprocs_def,toCong_def]
QED

(* Equality of semBakery$written and semCongBakery$written *)
Theorem written_eq:
  ∀τ. written τ = written (toCong τ)
Proof
  Cases_on `τ`
  >> rw [written_def,semBakeryTheory.written_def,toCong_def]
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
     \\ `p1 ∈ freeprocs τ'` by rw [freeprocs_eq]
     \\ `p2 ∉ freeprocs τ'` by rw [freeprocs_eq]
     \\ `written τ' ≠ SOME (v1,p1)` by rw [written_eq]
     \\ Cases_on ‘sender τ' = SOME p1’
     >- (EVERY (map Q.EXISTS_TAC [`LCom p1 v1 p2 v2 :: l`,`τ'`,`Com p1 v1 p2 v2 c''`])
        \\ metis_tac [scong_rules,trans_rules])
     \\ Cases_on ‘receiver τ' = SOME p1’
     >- (EVERY (map Q.EXISTS_TAC [`l`,`τ'`,`Com p1 v1 p2 v2 c''`])
        \\ metis_tac [scong_rules,trans_rules])
     \\ fs [semBakeryTheory.freeprocs_eq])
  >- (rfs []
     \\ `p1 ∈ freeprocs τ'` by rw [freeprocs_eq]
     \\ `p2 ∉ freeprocs τ'` by rw [freeprocs_eq]
     \\ Cases_on ‘sender τ' = SOME p1’
     >- (EVERY (map Q.EXISTS_TAC [`LSel p1 b p2 :: l`,`τ'`,`Sel p1 b p2 c''`])
        \\ metis_tac [scong_rules,trans_rules])
     \\ Cases_on ‘receiver τ' = SOME p1’
     >- (EVERY (map Q.EXISTS_TAC [`l`,`τ'`,`Sel p1 b p2 c''`])
        \\ metis_tac [scong_rules,trans_rules])
     \\ fs [semBakeryTheory.freeprocs_eq])
  \\ rfs []
  \\ last_assum (ASSUME_TAC o MATCH_MP trans_from_cong)
  \\ RES_TAC
  \\ EVERY (map Q.EXISTS_TAC [`l`,`τ'`,`c2`])
  \\ rw []
  \\ IMP_RES_TAC scong_refl
  \\ IMP_RES_TAC scong_trans
  \\ IMP_RES_TAC trans_imp_chorTrm
  \\ rw []
  \\ match_mp_tac scong_trans
  \\ Q.EXISTS_TAC `chorTrm s τ' c''`
  \\ rw [chorTrm_scong]
QED

val _ = export_theory()
