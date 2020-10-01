open preamble

open chorSemTheory chorPropsTheory
open chorCongSemTheory chorLangTheory
open choreoUtilsTheory

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

(* A linear congruence is a pre-congruence  *)
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

(* An unfolding is a pre-congruence *)
Theorem flcong_scong:
  ∀c c'. c ≅⟩ c' ⇒ c ≲ c'
Proof
  ho_match_mp_tac flcong_strongind
  \\ rw [scong_rules]
  \\ metis_tac [scong_rules]
QED

(* Unfolding does not re-arrange communications *)
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

(* Unfolding does not re-arrange selections *)
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

(* Unfolding does not re-arrange let-bindings *)
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

(* Unfolding does not re-arrange branches *)
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

(* Nil can only unfold to Nil *)
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

(* Call can only unfold to Call *)
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

(* One can either unfold Fix or do nothing *)
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

(* One can always group unfolding at the front
   of linear congruence. Also implies unfolding
   can (if done the same number of times) preserve
   swapping (linear congruence)
 *)
Theorem flcong_lncong:
∀c1 c2 c3.
    c1 ≅l c2 ∧ c2 ≅⟩ c3
    ⇒ ∃c. c1 ≅⟩ c ∧ c ≅l c3
Proof
  metis_tac [flcong_lncong_aux,flcong_refl]
QED

(* scong can be split into an unfolding relations and linear
   congruence (no unfolding).

   *NOTE*: The most interesting thing about this lemma is that
           whatever happens in scong can be grouped into first some
           unfoldings and then all the swapping required.
*)
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
  ∀τ τ'. toCong τ = SOME τ' ⇒ freeprocs τ = freeprocs τ'
Proof
  Cases
  >> rw [freeprocs_def,chorSemTheory.freeprocs_def,toCong_def]
  >> rw [freeprocs_def,chorSemTheory.freeprocs_def,toCong_def]
QED

(* Equality of chorSem$written and chorTrm$written *)
Theorem written_eq:
  ∀τ τ'. toCong τ = SOME τ' ⇒ written τ = written τ'
Proof
  Cases
  >> rw [written_def,chorSemTheory.written_def,toCong_def]
  >> rw [written_def,chorSemTheory.written_def,toCong_def]
QED

(* Unfolding transition do not change the state ” *)
Theorem trans_LFix_state:
  ∀s c s' c'.
    trans (s,c) (LFix,[]) (s',c')
    ⇒ s = s'
Proof
  ‘∀s c τ l s' c'.
     trans (s,c) (τ,l) (s',c')
     ⇒ τ = LFix ∧ l = []
     ⇒ s = s'’
  suffices_by metis_tac []
  \\ ho_match_mp_tac trans_pairind
  \\ rw []
QED

(* Unfolding transitions can jump over communications *)
Theorem trans_unfold_com_swap:
  ∀s c c' p1 v1 p2 v2.
    trans_unfold (s,c) (s,c')
    ⇒ trans_unfold (s,Com p1 v1 p2 v2 c) (s,Com p1 v1 p2 v2 c')
Proof
  rw [trans_unfold_def]
  \\ qmatch_goalsub_abbrev_tac ‘RTC r0 (s,com c)’
  \\ ‘RTC r0 (s,com c) (s,com c') = (λ(s,c) (s',c'). r0꙳ (s,com c) (s',com c')) (s,c) (s,c')’ by simp []
  \\ pop_assum (ONCE_REWRITE_TAC o single)
  \\ qmatch_asmsub_abbrev_tac ‘RTC r0 a0 a1’
  \\ ‘FST a0 = FST a1’ by (UNABBREV_ALL_TAC \\ rw [])
  \\ pop_assum mp_tac
  \\ last_x_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘a0’,‘a1’])
  \\ ho_match_mp_tac RTC_ind
  \\ UNABBREV_ALL_TAC
  \\ rw []
  >- (Cases_on ‘a0’ \\ simp [])
  \\ PairCases_on ‘a0’ \\ PairCases_on ‘a1’
  \\ PairCases_on ‘a0'’  \\ fs []
  \\ qmatch_asmsub_rename_tac ‘trans (s,c) _ (s',c')’
  \\ drule trans_LFix_state \\ rw []
  \\ qmatch_asmsub_rename_tac ‘RTC _ _ (s,_ c'')’
  \\ ho_match_mp_tac RTC_TRANS
  \\ qexists_tac ‘(s,Com p1 v1 p2 v2 c')’
  \\ rw [trans_com_swap,chorSemTheory.freeprocs_def]
QED

(* Unfolding transitions can jump over selections *)
Theorem trans_unfold_sel_swap:
  ∀s c c' p1 b p2.
    trans_unfold (s,c) (s,c')
    ⇒ trans_unfold (s,Sel p1 b p2 c) (s,Sel p1 b p2 c')
Proof
  rw [trans_unfold_def]
  \\ qmatch_goalsub_abbrev_tac ‘RTC r0 (s,com c)’
  \\ ‘RTC r0 (s,com c) (s,com c') = (λ(s,c) (s',c'). r0꙳ (s,com c) (s',com c')) (s,c) (s,c')’ by simp []
  \\ pop_assum (ONCE_REWRITE_TAC o single)
  \\ qmatch_asmsub_abbrev_tac ‘RTC r0 a0 a1’
  \\ ‘FST a0 = FST a1’ by (UNABBREV_ALL_TAC \\ rw [])
  \\ pop_assum mp_tac
  \\ last_x_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘a0’,‘a1’])
  \\ ho_match_mp_tac RTC_ind
  \\ UNABBREV_ALL_TAC
  \\ rw []
  >- (Cases_on ‘a0’ \\ simp [])
  \\ PairCases_on ‘a0’ \\ PairCases_on ‘a1’
  \\ PairCases_on ‘a0'’  \\ fs []
  \\ qmatch_asmsub_rename_tac ‘trans (s,c) _ (s',c')’
  \\ drule trans_LFix_state \\ rw []
  \\ qmatch_asmsub_rename_tac ‘RTC _ _ (s,_ c'')’
  \\ ho_match_mp_tac RTC_TRANS
  \\ qexists_tac ‘(s,Sel p1 b p2 c')’
  \\ rw [trans_sel_swap,chorSemTheory.freeprocs_def]
QED

(* Unfolding transitions can jump over let bindings *)
Theorem trans_unfold_let_swap:
  ∀s c c' v p f vl.
    trans_unfold (s,c) (s,c')
    ⇒ trans_unfold (s,Let v p f vl c) (s,Let v p f vl c')
Proof
  rw [trans_unfold_def]
  \\ qmatch_goalsub_abbrev_tac ‘RTC r0 (s,com c)’
  \\ ‘RTC r0 (s,com c) (s,com c') = (λ(s,c) (s',c'). r0꙳ (s,com c) (s',com c')) (s,c) (s,c')’ by simp []
  \\ pop_assum (ONCE_REWRITE_TAC o single)
  \\ qmatch_asmsub_abbrev_tac ‘RTC r0 a0 a1’
  \\ ‘FST a0 = FST a1’ by (UNABBREV_ALL_TAC \\ rw [])
  \\ pop_assum mp_tac
  \\ last_x_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘a0’,‘a1’])
  \\ ho_match_mp_tac RTC_ind
  \\ UNABBREV_ALL_TAC
  \\ rw []
  >- (Cases_on ‘a0’ \\ simp [])
  \\ PairCases_on ‘a0’ \\ PairCases_on ‘a1’
  \\ PairCases_on ‘a0'’  \\ fs []
  \\ qmatch_asmsub_rename_tac ‘trans (s,c) _ (s',c')’
  \\ drule trans_LFix_state \\ rw []
  \\ qmatch_asmsub_rename_tac ‘RTC _ _ (s,_ c'')’
  \\ ho_match_mp_tac RTC_TRANS
  \\ qexists_tac ‘(s,Let v p f vl c')’
  \\ rw [trans_let_swap,chorSemTheory.freeprocs_def]
QED

(* Unfolding transitions can jump over branches *)
Theorem trans_unfold_if_swap:
  ∀s c1 c1' c2 c2' e p.
    trans_unfold (s,c1) (s,c1') ∧
    trans_unfold (s,c2) (s,c2')
    ⇒ trans_unfold (s,IfThen e p c1 c2) (s,IfThen e p c1' c2')
Proof
  rw [trans_unfold_def]
  \\ qmatch_goalsub_abbrev_tac ‘RTC r0 (s,iff c1 c2)’
  \\ irule RTC_SPLIT
  \\ qexists_tac ‘(s,iff c1' c2)’
  \\ conj_tac
  >- (‘RTC r0 (s,iff c1 c2) (s,iff c1' c2) =
        (λ(s,c1) (s',c1'). r0꙳ (s,iff c1 c2) (s',iff c1' c2)) (s,c1) (s,c1')’ by simp []
      \\ pop_assum (ONCE_REWRITE_TAC o single)
      \\ Q.ABBREV_TAC ‘a0 = (s,c1)’
      \\ Q.ABBREV_TAC ‘a1 = (s,c1')’
      \\ ‘FST a0 = FST a1’ by (UNABBREV_ALL_TAC \\ rw [])
      \\ pop_assum mp_tac
      \\ last_x_assum mp_tac
      \\ ntac 2 (pop_assum kall_tac)
      \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘a0’,‘a1’])
      \\ qpat_x_assum ‘RTC _ _ _’ kall_tac
      \\ ho_match_mp_tac RTC_ind
      \\ UNABBREV_ALL_TAC
      \\ rw []
      >- (Cases_on ‘a0’ \\ simp [])
      \\ PairCases_on ‘a0’ \\ PairCases_on ‘a1’
      \\ PairCases_on ‘a0'’  \\ fs []
      \\ qmatch_asmsub_rename_tac ‘trans (s,c) _ (s',c')’
      \\ drule trans_LFix_state \\ rw []
      \\ qmatch_asmsub_rename_tac ‘RTC _ _ (s,_ c'')’
      \\ ho_match_mp_tac RTC_TRANS
      \\ qexists_tac ‘(s,IfThen e p c' c'')’
      \\ rw [trans_fix_if_true])
  \\ ‘RTC r0 (s,iff c1' c2) (s,iff c1' c2') =
      (λ(s,c2) (s',c2'). r0꙳ (s,iff c1' c2) (s',iff c1' c2')) (s,c2) (s,c2')’ by simp []
  \\ pop_assum (ONCE_REWRITE_TAC o single)
  \\ Q.ABBREV_TAC ‘a0 = (s,c2)’
  \\ Q.ABBREV_TAC ‘a1 = (s,c2')’
  \\ ‘FST a0 = FST a1’ by (UNABBREV_ALL_TAC \\ rw [])
  \\ pop_assum mp_tac
  \\ qpat_x_assum ‘RTC _ (s,_) _’ kall_tac
  \\ last_x_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘a0’,‘a1’])
  \\ ho_match_mp_tac RTC_ind
  \\ UNABBREV_ALL_TAC
  \\ rw []
  >- (Cases_on ‘a0’ \\ simp [])
  \\ PairCases_on ‘a0’ \\ PairCases_on ‘a1’
  \\ PairCases_on ‘a0'’  \\ fs []
  \\ qmatch_asmsub_rename_tac ‘trans (s,c) _ (s',c')’
  \\ drule trans_LFix_state \\ rw []
  \\ qmatch_asmsub_rename_tac ‘RTC _ _ (s,_ c'')’
  \\ ho_match_mp_tac RTC_TRANS
  \\ qexists_tac ‘(s,IfThen e p c1' c')’
  \\ rw [trans_fix_if_false]
QED

(* The unfolding relation implies unfolding transitions exists such
   that ‘c’ can reach ‘c'’
*)
Theorem flcong_trans_unfold:
  ∀s c c'.
    c ≅⟩ c' ⇒ trans_unfold (s,c) (s,c')
Proof
  GEN_TAC
  \\ ho_match_mp_tac flcong_strongind \\ rw []
  >- rw [trans_unfold_def]
  >- (fs [trans_unfold_def] \\ metis_tac [RTC_SPLIT])
  >- metis_tac [trans_unfold_if_swap]
  >- metis_tac [trans_unfold_let_swap]
  >- metis_tac [trans_unfold_com_swap]
  >- metis_tac [trans_unfold_sel_swap]
  \\ simp [trans_unfold_def]
  \\ irule RTC_SINGLE
  \\ rw [trans_fix]
QED

(* A single unfolding transition implies an unfolding relation exists
   between ‘c’ and ‘c'’
*)
Theorem trans_LFix_flcong:
  ∀s c c'.
    trans (s,c) (LFix,[]) (s,c')
    ⇒ c ≅⟩ c'
Proof
  ‘∀s c τ l s' c'.
     trans (s,c) (τ,l) (s',c')
     ⇒ s' = s ∧ τ = LFix ∧ l = []
     ⇒ c ≅⟩ c'’
  suffices_by metis_tac []
  \\ ho_match_mp_tac trans_pairind
  \\ rw [flcong_rules]
  \\ gs [lcong_nil_simp]
  \\ metis_tac [flcong_rules]
QED

(* Multiple unfolding transitions imply an unfolding relation exists
   between ‘c’ and ‘c'’
*)
Theorem trans_unfold_flcong:
  ∀s c c'.
    trans_unfold (s,c) (s,c') ⇒ c ≅⟩ c'
Proof
  rw [trans_unfold_def]
  \\ qmatch_asmsub_abbrev_tac ‘RTC r0 a0 a1’
  \\ ‘(λ(s,c) (s',c'). c ≅⟩ c') a0 a1’ suffices_by (UNABBREV_ALL_TAC \\ simp [])
  \\ ‘FST a0 = FST a1’ by (UNABBREV_ALL_TAC \\ simp [])
  \\ pop_assum mp_tac
  \\ last_x_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ MAP_EVERY (W(curry Q.SPEC_TAC)) (rev [‘a0’,‘a1’])
  \\ ho_match_mp_tac RTC_ind
  \\ UNABBREV_ALL_TAC
  \\ rw []
  >- (Cases_on ‘a0’ \\ simp [flcong_refl])
  \\ PairCases_on ‘a0’ \\ PairCases_on ‘a1’
  \\ PairCases_on ‘a0'’  \\ fs []
  \\ metis_tac [trans_LFix_state,trans_LFix_flcong,flcong_trans]
QED

(* Given a linear congruence and the unfolding of one of the
   choreographies there exists an unfolding that preserves
   the liner congruence. This lemma is just ‘flcong_lncong’
   with ‘trans_unfold’ instead of ‘flcong’
 *)
Theorem trans_unfold_from_cong:
  ∀c1 c2 c3 s.
    c1 ≅l c2 ∧ trans_unfold (s,c2) (s,c3)
    ⇒ ∃c4. trans_unfold (s,c1) (s,c4) ∧ c3 ≅l c4
Proof
  metis_tac [flcong_trans_unfold,lncong_sym,flcong_lncong,trans_unfold_flcong]
QED

(* Transitivity of trans_unfold *)
Theorem trans_unfold_trans:
  ∀a b c.
    trans_unfold a b ∧ trans_unfold b c
    ⇒ trans_unfold a c
Proof
  rw [trans_unfold_def]
  \\ metis_tac [RTC_SPLIT]
QED

(* `transCong` implies `trans` up to unfolding on both sides of the
   resulting choreography and ‘≅’ at the end.

   .-----------------------transCong---------------------------> (c')
   |                                                              |
  (c)                                                            ≅l
   |                                                              |
   '---trans_unfold--> (c0) ---trans--> (c1) ---trans_unfold---> (c2)

   having the lncong at the end means no extra unfolding is required
*)
Theorem transCong_imp_trans_aux:
   ∀s c τ s' c'.
    transCong (s,c) τ (s',c')
    ⇒ ∃l τ' c0 c1 c2.
        trans_unfold (s,c) (s,c0) ∧
        trans (s,c0) (τ',l) (s',c1) ∧
        trans_unfold (s',c1) (s',c2) ∧
        c' ≅l c2 ∧
        toCong τ' = SOME τ
Proof
  ho_match_mp_tac transCong_pairind
  \\ rw [toCong_def]
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LCom p1 v1 p2 v2`,`Com p1 v1 p2 v2 c'`,‘c'’,‘c'’])
     \\ rw [lncong_rules,trans_rules,toCong_def,trans_unfold_def,RTC_REFL])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LSel p1 b p2`,‘Sel p1 b p2 c'’,`c'`,`c'`])
     \\ rw [lncong_rules,trans_rules,toCong_def,trans_unfold_def])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LLet v p f vl`,‘Let v p f vl c'’,`c'`,`c'`])
     \\ rw [lncong_rules,trans_rules,toCong_def,trans_unfold_def])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LTau p v`,‘IfThen v p c' c2’,`c'`,`c'`])
     \\ rw [lncong_rules,trans_rules,toCong_def,trans_unfold_def])
  >- (EVERY (map Q.EXISTS_TAC [`[]`,`LTau p v`,‘IfThen v p c1 c'’,`c'`,`c'`])
     \\ rw [lncong_rules,trans_rules,toCong_def,trans_unfold_def])
  >- (rfs []
     \\ EVERY (map Q.EXISTS_TAC [`LCom p1 v1 p2 v2 :: l`,`τ'`,
                                 `Com p1 v1 p2 v2 c0`,
                                 `Com p1 v1 p2 v2 c1`,
                                 `Com p1 v1 p2 v2 c2`])
     \\ rw [lncong_rules,trans_unfold_com_swap]
     \\ `p1 ∈ freeprocs τ'` by metis_tac [freeprocs_eq]
     \\ `p2 ∉ freeprocs τ'` by metis_tac [freeprocs_eq]
     \\ `written τ' ≠ SOME (v1,p1)` by metis_tac [written_eq]
     \\ rw [trans_rules])
  >- (rfs []
     \\ EVERY (map Q.EXISTS_TAC [`LSel p1 b p2 :: l`,`τ'`,
                                 `Sel p1 b p2 c0`,
                                 `Sel p1 b p2 c1`,
                                 `Sel p1 b p2 c2`])
     \\ rw [lncong_rules,trans_unfold_sel_swap]
     \\ `p1 ∈ freeprocs τ'` by metis_tac [freeprocs_eq]
     \\ `p2 ∉ freeprocs τ'` by metis_tac [freeprocs_eq]
     \\ rw [trans_rules])
  \\ ‘c ≲ c0’ by metis_tac [scong_trans,flcong_scong,trans_unfold_flcong]
  \\ drule scong_lncong_flcong \\ rw []
  \\ drule flcong_trans_unfold
  \\ disch_then (qspec_then ‘s’ assume_tac)
  \\ asm_exists_tac \\ simp []
  \\ ‘τ' ≠ LFix’ by (Cases_on ‘τ'’ \\ fs [toCong_def])
  \\ drule trans_from_cong
  \\ disch_then (drule_then (qspecl_then [‘s’,‘s'’] assume_tac))
  \\ RES_TAC \\ asm_exists_tac \\ simp []
  \\ ‘c2' ≅l c1’ by metis_tac [lncong_sym,chorTrm_lncong,trans_imp_chorTrm]
  \\ drule trans_unfold_from_cong \\ disch_then drule \\ rw []
  \\ qpat_x_assum ‘_ ≲ c'’ (mp_then Any assume_tac scong_lncong_flcong)
  \\ fs []
  \\ ‘c4 ≅l c'''’ by metis_tac [lncong_rules]
  \\ drule flcong_lncong \\ disch_then drule
  \\ rw [] \\ qmatch_asmsub_rename_tac ‘c6 ≅l c5’
  \\ ‘c' ≅l c6’ by metis_tac [lncong_rules]
  \\ qexists_tac ‘c6’ \\ simp []
  \\ metis_tac [trans_unfold_trans,flcong_trans_unfold]
QED

(* A congruence is just a reflexive pre-congruence *)
Definition full_cong_def:
  full_cong c c' = (c ≲ c' ∧ c' ≲ c)
End

val _ = Parse.add_infix("≅",425,Parse.NONASSOC);
val _ = Parse.overload_on("≅",``full_cong``);

(* A linear congruence is a real congruence (dah!) *)
Theorem lncong_full_cong:
  ∀c c'. c ≅l c' ⇒ c ≅ c'
Proof
  rw [full_cong_def] \\ metis_tac [lncong_scong,lncong_sym]
QED

(* trans_unfold_trans_aux but using full_cong instead of lncong *)
Theorem transCong_imp_trans:
   ∀s c τ s' c'.
    transCong (s,c) τ (s',c')
    ⇒ ∃l τ' c0 c1 c2.
        trans_unfold (s,c) (s,c0) ∧
        trans (s,c0) (τ',l) (s',c1) ∧
        trans_unfold (s',c1) (s',c2) ∧
        c' ≅ c2 ∧
        toCong τ' = SOME τ
Proof
  metis_tac [transCong_imp_trans_aux,lncong_full_cong]
QED

val _ = export_theory()
