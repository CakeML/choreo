open preamble

open chorSemTheory chorPropsTheory chorCongSemTheory chorLangTheory

val _ = new_theory "congProof";

(* chorSem$label to chorCongSem$label conversion *)
Definition toCong_def:
  toCong (LTau p v)      = SOME (LTau p NONE)
∧ toCong (LCom p v q v') = SOME (LCom p v q v')
∧ toCong (LSel p b q)    = SOME (LSel p b q)
∧ toCong (LLet v p f vl) = SOME (LTau p (SOME v))
∧ toCong _               = NONE
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
∧ chorTrm s LFix (Fix x c)         = dsubst c x (Fix x c)
∧ chorTrm s τ (Com p' v' q' x' c)  = Com p' v' q' x' (chorTrm s τ c)
∧ chorTrm s τ (Sel p' b' q' c)     = Sel p' b' q' (chorTrm s τ c)
∧ chorTrm s τ (Let v' p' f' vl' c) = Let v' p' f' vl' (chorTrm s τ c)
∧ chorTrm s τ (IfThen v' p' c1 c2) = IfThen v' p' (chorTrm s τ c1) (chorTrm s τ c2)
∧ chorTrm s τ (Fix x c)            = (Fix x c)
∧ chorTrm s τ (Call x)             = (Call x)
∧ chorTrm s τ Nil                  = Nil
End

Theorem lncong_scong:
  ∀c c'. c ≅l c'  ⇒ c ≲ c'
Proof
  ‘∀c c'. c ≅l c'  ⇒ c ≲ c' ∧ c' ≲ c’
  suffices_by metis_tac []
  \\ ho_match_mp_tac lncong_strongind
  \\ rw [scong_rules]
  \\ TRY ((irule scong_com_swap ORELSE irule scong_sel_swap)
          \\ fs [INTER_DEF,EMPTY_DEF,FUN_EQ_THM]
          \\ metis_tac [])
  \\ metis_tac [scong_rules]
QED

Theorem flcong_scong:
  ∀c c'. c ≅⟩ c' ⇒ c ≲ c'
Proof
  ho_match_mp_tac flcong_strongind
  \\ rw [scong_rules]
  \\ metis_tac [scong_rules]
QED

Theorem Com_flcong:
  ∀p1 v1 p2 v2 c c'.
    Com p1 v1 p2 v2 c ≅⟩ c'
    ⇒ ∃c''. c' = Com p1 v1 p2 v2 c'' ∧ c ≅⟩ c''
Proof
  ‘∀c1 c2.
     c1 ≅⟩ c2
     ⇒ ∀p1 v1 p2 v2 c.
         c1 = Com p1 v1 p2 v2 c
         ⇒ ∃c'. c2 = Com p1 v1 p2 v2 c' ∧ c ≅⟩ c'’
  suffices_by metis_tac []
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  \\ metis_tac [flcong_rules]
QED

Theorem Sel_flcong:
  ∀p1 b p2 c c'.
    Sel p1 b p2 c ≅⟩ c'
    ⇒ ∃c''. c' = Sel p1 b p2 c'' ∧ c ≅⟩ c''
Proof
  ‘∀c1 c2.
     c1 ≅⟩ c2
     ⇒ ∀p1 b p2 c.
         c1 = Sel p1 b p2 c
         ⇒ ∃c'. c2 = Sel p1 b p2 c' ∧ c ≅⟩ c'’
  suffices_by metis_tac []
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  \\ metis_tac [flcong_rules]
QED

Theorem Let_flcong:
  ∀p v f vl c c'.
    Let v p f vl c ≅⟩ c'
    ⇒ ∃c''. c' = Let v p f vl c'' ∧ c ≅⟩ c''
Proof
  ‘∀c1 c2.
     c1 ≅⟩ c2
     ⇒ ∀v p f vl c.
         c1 = Let v p f vl c
         ⇒ ∃c'. c2 = Let v p f vl c' ∧ c ≅⟩ c'’
  suffices_by metis_tac []
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  \\ metis_tac [flcong_rules]
QED

Theorem If_flcong:
  ∀v p c1 c2 c'.
    IfThen v p c1 c2 ≅⟩ c'
    ⇒ ∃c1' c2'. c' = IfThen v p c1' c2' ∧ c1 ≅⟩ c1' ∧ c2 ≅⟩ c2'
Proof
  ‘∀cl cr.
     cl ≅⟩ cr
     ⇒ ∀v p c1 c2.
         cl = IfThen v p c1 c2
         ⇒ ∃c1' c2'. cr = IfThen v p c1' c2' ∧ c1 ≅⟩ c1' ∧ c2 ≅⟩ c2'’
  suffices_by metis_tac []
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  \\ metis_tac [flcong_rules]
QED

Theorem Nil_flcong:
  ∀c'.
    Nil ≅⟩ c'
    ⇒ c' = Nil
Proof
  ‘∀cl cr.
     cl ≅⟩ cr
     ⇒ cl = Nil
         ⇒ cr = Nil’
  suffices_by metis_tac []
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  \\ metis_tac [flcong_rules]
QED

Theorem Call_flcong:
  ∀c' x.
    Call x ≅⟩ c'
    ⇒ c' = Call x
Proof
  ‘∀cl cr.
     cl ≅⟩ cr
     ⇒ ∀x. cl = Call x
         ⇒ cr = Call x’
  suffices_by metis_tac []
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  \\ metis_tac [flcong_rules]
QED

Theorem Fix_flcong:
  ∀c c' x.
  Fix x c ≅⟩ c'
    ⇒ dsubst c x (Fix x c) ≅⟩ c' ∨ c' = Fix x c
Proof
  ‘∀cl cr.
     cl ≅⟩ cr
     ⇒ ∀x c. cl = Fix x c
         ⇒ dsubst c x (Fix x c) ≅⟩ cr ∨ cr = Fix x c’
  suffices_by metis_tac []
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  \\ metis_tac [flcong_rules]
QED

(* Confluence of fixpoint unfolding *)
Theorem flcong_confluence:
  ∀c c1 c2.
    c ≅⟩ c1 ∧ c ≅⟩ c2
    ⇒ ∃c3. c1 ≅⟩ c3 ∧ c2 ≅⟩ c3
Proof
  rw []
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (‘c2’,‘c2’)
  \\ pop_assum mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘c’,‘c1’])
  \\ ho_match_mp_tac flcong_strongind
  \\ rw [flcong_rules]
  >- (qexists_tac ‘c2’ \\ rw [flcong_refl])
  >- metis_tac [flcong_rules]
  >- (drule If_flcong \\ rw []
      \\ first_x_assum drule
      \\ first_x_assum drule
      \\ rw []
      \\ metis_tac [flcong_rules])
  >- metis_tac [flcong_rules,Let_flcong]
  >- metis_tac [flcong_rules,Com_flcong]
  >- metis_tac [flcong_rules,Sel_flcong]
  \\ metis_tac [flcong_rules,Fix_flcong]
QED

(* Auxiliar lemma to support doing unfoldings before instead of after a congruence *)
Theorem flcong_lncong_aux:
∀c1 c2 c3 c4.
    c1 ≅l c2 ∧ c2 ≅⟩ c3 ∧ c1 ≅⟩ c4
    ⇒ ∃c c'. c1 ≅⟩ c ∧ c ≅l c3 ∧ c2 ≅⟩ c' ∧ c' ≅l c4
Proof
  rpt strip_tac
  \\ pop_assum mp_tac \\ pop_assum mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘c3’,‘c4’])
  \\ pop_assum mp_tac
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘c1’,‘c2’])
  \\ ho_match_mp_tac lncong_strongind
  \\ rw [lncong_rules,flcong_rules]
  >- metis_tac [lncong_rules,flcong_rules]
  >- metis_tac [lncong_rules,flcong_rules]
  >- (last_assum (qspec_then ‘c1'’ mp_tac)
      \\ disch_then (qspec_then ‘c4’ mp_tac)
      \\ impl_tac >- simp [flcong_refl]
      \\ disch_then drule
      \\ rw []
      \\ first_assum (qspecl_then [‘c3’,‘c1'’] mp_tac)
      \\ impl_tac >- simp [flcong_refl]
      \\ impl_tac >- simp [flcong_refl]
      \\ rw []
      \\ ‘(∃c. c1 ≅⟩ c ∧ c ≅l c3) ∧ (∃c'. c2 ≅⟩ c' ∧ c' ≅l c4)’
         suffices_by metis_tac []
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Com_flcong \\ dxrule Com_flcong \\ rw []
      \\ dxrule Com_flcong \\ dxrule Com_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘f (g c) ≅⟩ _’
      \\ qexists_tac ‘f (g c'''')’
      \\ qexists_tac ‘g (f c''''')’
      \\ UNABBREV_ALL_TAC
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Sel_flcong \\ dxrule Com_flcong \\ rw []
      \\ dxrule Com_flcong \\ dxrule Sel_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘f (g c) ≅⟩ _’
      \\ qexists_tac ‘f (g c''''')’
      \\ qexists_tac ‘g (f c'''')’
      \\ UNABBREV_ALL_TAC
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Sel_flcong \\ dxrule Sel_flcong \\ rw []
      \\ dxrule Sel_flcong \\ dxrule Sel_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘f (g c) ≅⟩ _’
      \\ qexists_tac ‘f (g c'''')’
      \\ qexists_tac ‘g (f c''''')’
      \\ UNABBREV_ALL_TAC
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Let_flcong \\ dxrule Com_flcong \\ rw []
      \\ dxrule Com_flcong \\ dxrule Let_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘w (g c) ≅⟩ _’
      \\ qexists_tac ‘w (g c''''')’
      \\ qexists_tac ‘g (w c'''')’
      \\ UNABBREV_ALL_TAC
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Let_flcong \\ dxrule Let_flcong \\ rw []
      \\ dxrule Let_flcong \\ dxrule Let_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘w (g c) ≅⟩ _’
      \\ qexists_tac ‘w (g c'''')’
      \\ qexists_tac ‘g (w c''''')’
      \\ UNABBREV_ALL_TAC
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Let_flcong \\ dxrule Sel_flcong \\ rw []
      \\ dxrule Sel_flcong \\ dxrule Let_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘w (g c) ≅⟩ _’
      \\ qexists_tac ‘w (g c''''')’
      \\ qexists_tac ‘g (w c'''')’
      \\ UNABBREV_ALL_TAC
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule If_flcong \\ dxrule If_flcong \\ rw []
      \\ dxrule If_flcong \\ dxrule If_flcong \\ rw []
      \\ dxrule If_flcong \\ dxrule If_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘f (g c1 c2) _ ≅⟩ _’
      \\ qmatch_goalsub_rename_tac ‘_ ≅l g (f c10 c10') (f c20 c20')’
      \\ qmatch_goalsub_rename_tac ‘_ ≅l f (g c11 c21) (g c11' c21')’
      \\ rw []
      \\ qexists_tac ‘f (g c10 c20)  (g c10' c20')’
      \\ qexists_tac ‘g (f c11 c11') (f c21  c21')’
      \\ UNABBREV_ALL_TAC
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule If_flcong \\ dxrule Com_flcong \\ rw []
      \\ dxrule If_flcong \\ dxrule Com_flcong
      \\ dxrule Com_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘f (g c1 c2) ≅⟩ _’
      \\ qmatch_goalsub_rename_tac ‘_ ≅l g (f c1') (f c2')’
      \\ qexists_tac ‘f (g c1' c2')’
      \\ qexists_tac ‘g (f c1'') (f c2'')’
      \\ UNABBREV_ALL_TAC \\ rw []
      >- metis_tac [flcong_rules]
      >- (irule lncong_com_if_swap \\ rw [IN_DEF])
      >- metis_tac [flcong_rules]
      \\ (irule lncong_sym \\ irule lncong_com_if_swap \\ rw [IN_DEF]))
  >- (dxrule If_flcong \\ dxrule Sel_flcong \\ rw []
      \\ dxrule If_flcong \\ dxrule Sel_flcong
      \\ dxrule Sel_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘f (g c1 c2) ≅⟩ _’
      \\ qmatch_goalsub_rename_tac ‘_ ≅l g (f c1') (f c2')’
      \\ qexists_tac ‘f (g c1' c2')’
      \\ qexists_tac ‘g (f c1'') (f c2'')’
      \\ UNABBREV_ALL_TAC \\ rw []
      >- metis_tac [flcong_rules]
      >- (irule lncong_sel_if_swap \\ rw [IN_DEF])
      >- metis_tac [flcong_rules]
      \\ (irule lncong_sym \\ irule lncong_sel_if_swap \\ rw [IN_DEF]))
  >- (dxrule If_flcong \\ dxrule Let_flcong \\ rw []
      \\ dxrule If_flcong \\ dxrule Let_flcong
      \\ dxrule Let_flcong \\ rw []
      \\ qmatch_goalsub_abbrev_tac ‘w (g c1 c2) ≅⟩ _’
      \\ qmatch_goalsub_rename_tac ‘_ ≅l g (w c1') (w c2')’
      \\ qexists_tac ‘w (g c1' c2')’
      \\ qexists_tac ‘g (w c1'') (w c2'')’
      \\ UNABBREV_ALL_TAC \\ rw []
      >- metis_tac [flcong_rules]
      >- (irule lncong_let_if_swap \\ rw [IN_DEF])
      >- metis_tac [flcong_rules]
      \\ (irule lncong_sym \\ irule lncong_let_if_swap \\ rw [IN_DEF]))
  >- (dxrule If_flcong \\ dxrule If_flcong \\ rw []
      \\ first_x_assum drule_all
      \\ first_x_assum drule_all
      \\ rw []
      \\ qexists_tac ‘IfThen e p c c''’
      \\ qexists_tac ‘IfThen e p c' c'''’
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Let_flcong \\ dxrule Let_flcong \\ rw []
      \\ first_x_assum drule_all \\ rw []
      \\ qexists_tac ‘Let v p f vl c’
      \\ qexists_tac ‘Let v p f vl c'’
      \\ metis_tac [lncong_rules,flcong_rules])
  >- (dxrule Com_flcong \\ dxrule Com_flcong \\ rw []
      \\ first_x_assum drule_all \\ rw []
      \\ qexists_tac ‘Com p1 v1 p2 v2 c’
      \\ qexists_tac ‘Com p1 v1 p2 v2 c'’
      \\ metis_tac [lncong_rules,flcong_rules])
  \\ dxrule Sel_flcong \\ dxrule Sel_flcong \\ rw []
      \\ first_x_assum drule_all \\ rw []
      \\ qexists_tac ‘Sel p1 b p2  c’
      \\ qexists_tac ‘Sel p1 b p2  c'’
      \\ metis_tac [lncong_rules,flcong_rules]
QED

(* One can always find an unfolding such that it can be done before
   instead of after a given congruence
 *)
Theorem flcong_lncong:
∀c1 c2 c3.
    c1 ≅l c2 ∧ c2 ≅⟩ c3
    ⇒ ∃c. c1 ≅⟩ c ∧ c ≅l c3
Proof
  metis_tac [flcong_lncong_aux,flcong_refl]
QED

(*  *)
Theorem scong_lncong_flcong:
  ∀c1 c2.
    c1 ≲ c2
    ⇒ ∃c. c1 ≅⟩ c ∧ c ≅l c2
Proof
  ho_match_mp_tac scong_strongind
  \\ rw [lncong_rules,flcong_rules]
  \\ TRY (qmatch_goalsub_abbrev_tac ‘cc ≅⟩ _’
          \\ qexists_tac ‘cc’
          \\ rw [Abbr‘cc’,lncong_rules,flcong_rules]
          \\ NO_TAC)
  \\ metis_tac [lncong_rules,flcong_rules,flcong_lncong]
QED

(* The application of `chorTrm` preserves `lncong` *)
Theorem chorTrm_lncong:
  ∀s τ c c'. c ≅l c' ⇒ chorTrm s τ c ≅l chorTrm s τ c'
Proof
  rpt GEN_TAC
  \\ `∀c c'.
        c ≅l c'
        ⇒ c ≅l c'
        ⇒ chorTrm s τ c ≅l chorTrm s τ c'`
     suffices_by (metis_tac [])
  \\ Cases_on `τ`
  \\ ho_match_mp_tac lncong_strongind
  \\ rw [chorTrm_def]
  \\ rfs [lncong_rules]
  \\ IMP_RES_TAC lncong_trans
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


     c1 ≅l c2 ∧ trans (s,c1) (τ,l) (s',c1') ∧ trans (s,c2) (τ,l') (s',c2')
    ----------------------------------------------------------------------
                             c1' ≅l c2'

   ‘trans_imp_chorTrm’ excludes LFix because there is more than 1
   possible choreography resulting from an LFix transition due to
   ‘trans_fix_if_true’ and ‘trans_fix_if_false’
*)
Theorem trans_imp_chorTrm:
   ∀s c τ l s' c'.
     trans (s,c) (τ,l) (s',c') ∧ τ ≠ LFix
    ⇒ c' = chorTrm s τ c
Proof
  rpt GEN_TAC
  \\ `∀s c τ' l s' c'.
       trans (s,c) (τ',l) (s',c')
       ⇒ τ' = τ ∧ τ ≠ LFix
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
    trans (s,c) (τ,l) (s',c') ∧ τ ≠ LFix ⇒ trans (s,c) (τ,l) (s',chorTrm s τ c)
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
    c1 ≅l c1'
    ⇒ (∀s s' τ c2 c2' l l'.
         τ ≠ LFix ⇒
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
  (ho_match_mp_tac lncong_ind
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
  >- (first_x_assum drule \\ first_x_assum drule
      \\ strip_tac \\ strip_tac
      \\ l_tac >- l_tac >- l_tac
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
    c1 ≅l c1' ∧ τ ≠ LFix
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
