open preamble bakery_to_halfTheory congProofTheory semBakeryTheory semHalfBakeryTheory

val _ = new_theory "bakery_to_halfProof"

val RTC_TRANS =  RTC_RULES |> CONV_RULE FORALL_AND_CONV
                           |> CONJUNCTS |> el 2;




val trans_cTrm_def = Define `
  
`
chorTrm_def

Theorem trans_async_complete:
  ∀s c α l ls s' c'.
   trans (s,c) (α,l::ls) (s',c')
   ⇒ trans (s',c') (l,ls) (state_from_tag s' l, chorTrm s' l c')
Proof
  `∀s c α τ s' c'. trans (s,c) (α,τ) (s',c')
    ⇒ ∀l ls. τ = l::ls
       ⇒ trans (s',c') (l,ls) (state_from_tag s' l, chorTrm s' l c')`
  suffices_by metis_tac []
  \\ ho_match_mp_tac semBakeryTheory.trans_pairind
  \\ rw []

QED




val pchorTrm_def = Define`
  pchorTrm s (semBakery$LCom p v q x) (Com p' v' q' x' c) =
    (if (p,v,q,x) = (p',v',q',x') then project c
     else if (p,v) = (p',v')
     then PCom q x (p, THE (FLOOKUP s (v,p))) (pchorTrm s (LCom p v q x) c)
     else Com p' v' q' x'     (pchorTrm s (LCom p v q x) c))
∧ pchorTrm s (LSel p b q) (Sel p' b' q' c) =
    (if (p,b,q) = (p',b',q') then project c
     else if (p,b) = (p',b')
     then PSel q (p, b) (pchorTrm s (LSel p b q) c)
     else Sel p' b' q'  (pchorTrm s (LSel p b q) c))
∧ pchorTrm s (LLet v p f vl) (Let v' p' f' vl' c) =
    (if (v,p,f,vl) = (v',p',f',vl') then project c
     else Let v' p' f' vl' (pchorTrm s (LLet v p f vl) c))
∧ pchorTrm s (LTau p v) (IfThen v' p' c1 c2) =
    (if (p,v) = (p',v')
     then if FLOOKUP s (v,p) = SOME [1w] then project c1
          else if ∃w. FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w] then project c2
          else IfThen v' p' (project c1) (project c2) (* Imposible? *)
     else IfThen v' p' (pchorTrm s (LTau p v) c1) (pchorTrm s (LTau p v) c2))
∧ pchorTrm s τ (Com p' v' q' x' c)  = Com p' v' q' x' (pchorTrm s τ c)
∧ pchorTrm s τ (Sel p' b' q' c)     = Sel p' b' q' (pchorTrm s τ c)
∧ pchorTrm s τ (Let v' p' f' vl' c) = Let v' p' f' vl' (pchorTrm s τ c)
∧ pchorTrm s τ (IfThen v' p' c1 c2) = IfThen v' p' (pchorTrm s τ c1) (pchorTrm s τ c2)
∧ pchorTrm s τ Nil                  = Nil
`;

val complete_pchor_def = Define `
  complete_pchor Nil                = astBakery$Nil
∧ complete_pchor (PCom q x (p,d) c) = complete_pchor c
∧ complete_pchor (PSel q (p,b) c)   = complete_pchor c
∧ complete_pchor (Com p v q x c)    = Com p v q x (complete_pchor c)
∧ complete_pchor (Sel p b q c)      = Sel p b q   (complete_pchor c)
∧ complete_pchor (Let v p f vl c)   = Let v p f vl (complete_pchor c)
∧ complete_pchor (IfThen v p c1 c2) = IfThen v p (complete_pchor c1) (complete_pchor c2)
`

Theorem complete_project_eq:
  ∀c. complete_pchor (project c) = c
Proof
  Induct \\ rw [complete_pchor_def,project_def]
QED

Theorem no_undefined_vars_from_tags:
  ∀c s α.
   no_undefined_vars (s,c) ⇒ no_undefined_vars (state_from_tag s α, c)
Proof
  rw [no_undefined_vars_def,free_variables_def]
  \\ Cases_on `α` \\ fs [state_from_tag_def]
  \\ ho_match_mp_tac SUBSET_TRANS
  \\ metis_tac [SUBSET_OF_INSERT]
QED

Theorem chorTrm_eq_pchorTrm:
  ∀c s α. chorTrm s α c = complete_pchor (pchorTrm s α c)


Theorem Trm_trans:
  ∀c s α. no_undefined_vars (state_from_tag s α,c) ∧ no_self_comunication c
   ⇒ ∃s'. trans_s (state_from_tag s α, chorTrm s α c) (s', complete_pchor (pchorTrm s α c))
Proof
  ho_match_mp_tac (theorem "pchorTrm_ind")
  \\ rw [chorTrm_def,pchorTrm_def,complete_pchor_def,complete_project_eq]
  \\ TRY (qmatch_goalsub_abbrev_tac `trans_s (s1,c1) (_,c1)`
         \\ qexists_tac `s1`
         \\ rw [semBakeryTheory.trans_s_def])
  >- (qmatch_asmsub_abbrev_tac `no_undefined_vars (s1,c)`
     \\ `no_undefined_vars (s1,c)`
        by (UNABBREV_ALL_TAC \\ fs [ no_undefined_vars_def,state_from_tag_def
                                   , free_variables_def,no_self_comunication_def]


  Induct
  \\ rw [chorTrm_def,pchorTrm_def,complete_pchor_def,complete_project_eq]
  >- (qexists_tac `state_from_tag s α` \\ rw [semBakeryTheory.trans_s_def])
  >- (`no_undefined_vars (state_from_tag s' α,c)  ∧
       no_undefined_vars (state_from_tag s' α,c') ∧
       no_self_comunication c    ∧
       no_self_comunication c'`
       by fs [ no_undefined_vars_def,free_variables_def
             , no_self_comunication_def,no_undefined_vars_from_tags]
     \\ first_x_assum drule \\ disch_then drule
     \\ first_x_assum drule \\ disch_then drule
     \\ rw []
     \\ Cases_on `∃p v. α = LTau v p` \\ rw []
     >- (Cases_on `(v,p) = (l,s)`
        \\ rw [chorTrm_def,pchorTrm_def,complete_pchor_def,pchorTrm_def,complete_project_eq]
        \\ TRY (qmatch_goalsub_abbrev_tac `trans_s (s1,c1) (_,c1)`
        \\ qexists_tac `s1`
        \\ rw [semBakeryTheory.trans_s_def])



complete_pchor_def




first_x_assum (drule_then ) rw []

rw []
     \\ cheat)
  \\ cheat
QED


Theorem Trm_preservation:
  ∀c s α τ.
   trans (s,c) (α,τ) (state_from_tag s α, chorTrm s α c) ∧
   no_undefined_vars (s,c) ∧
   no_self_comunication c
   ⇒ ∃s'. trans_s (state_from_tag s α, chorTrm s α c)
                  (s',complete_pchor (pchorTrm s α c)) ∧
          trans_s (s,project c)
                  (s',project (complete_pchor (pchorTrm s α c)))
Proof
  `∀s c α τ s1 c1.
    trans (s,c) (α,τ) (s1,c1)
    ⇒ (no_undefined_vars (s,c) ∧
       no_self_comunication c  ∧
       s1 = state_from_tag s α ∧
       c1 = chorTrm s α c
       ⇒ ∃s'. trans_s (state_from_tag s α, chorTrm s α c)
                      (s',complete_pchor (pchorTrm s α c)) ∧
              trans_s (s,project c)
                      (s',project (complete_pchor (pchorTrm s α c))))`
         suffices_by metis_tac []
  \\ ho_match_mp_tac semBakeryTheory.trans_pairind
  \\ rw [chorTrm_def,pchorTrm_def,complete_pchor_def]




Theorem preservation:
  ∀c s α τ s' c'.
   trans (s,c) (α,τ) (s',c') ∧
   no_undefined_vars (s,c) ∧
   no_self_comunication c
   ⇒ ∃c'' s''. trans_s (s',c') (s'',c'')
      ∧        trans_s (s,project c) (s'',project c'')
Proof
  `∀s c α τ s' c'.
   trans (s,c) (α,τ) (s',c')
   ⇒  no_undefined_vars (s,c) ∧
      no_self_comunication c
      ⇒ ∃c'' s''. trans_s (s',c') (s'',c'')
         ∧        trans_s (s,project c) (s'',project c'')`
  suffices_by metis_tac []
  \\ let
    val one2one = qmatch_goalsub_abbrev_tac `semBakery$trans_s (st,chor) _`
                  \\ map_every qexists_tac [`chor`,`st`]
                  \\ unabbrev_all_tac
                  \\ rw [trans_s_def,semBakeryTheory.trans_s_def]
                  \\ ho_match_mp_tac RTC_SINGLE
                  \\ metis_tac [trans_rules,project_def]
  in ho_match_mp_tac semBakeryTheory.trans_pairind \\ rw []
     >- one2one >- one2one >- one2one >- one2one >- one2one
  end
    (* IfThen swap *)
  >- (`no_undefined_vars (s,c)  ∧
          no_undefined_vars (s,c') ∧
          no_self_comunication c    ∧
          no_self_comunication c'`
          by fs [ no_undefined_vars_def,free_variables_def
                , no_self_comunication_def]
      \\ first_x_assum drule \\ disch_then drule
      \\ first_x_assum drule \\ disch_then drule
      \\ rw []
      \\ `∃d. FLOOKUP s' (v,p) = SOME d ∧ FLOOKUP s (v,p) = SOME d`
          by (drule trans_state
              \\ rw [] \\ fs []
              \\ Cases_on `α`
              \\ fs [ state_from_tag_def
                    , semBakeryTheory.freeprocs_def
                    , no_undefined_vars_def
                    , free_variables_def,FLOOKUP_DEF]
              \\ EVAL_TAC
              \\ fs [])
      \\ Cases_on `d = [1w]`
      >- (map_every qexists_tac [`c''''`,`s''`]
         \\ conj_tac
         >- (fs [semBakeryTheory.trans_s_def]
            \\ ho_match_mp_tac RTC_TRANS
            \\ metis_tac [semBakeryTheory.trans_rules])
         \\ rw [project_def]
         \\ fs [trans_s_def]
         \\ ho_match_mp_tac RTC_TRANS
         \\ metis_tac [trans_rules])
      >- (map_every qexists_tac [`c'''''`,`s'''`]
         \\ conj_tac
         >- (fs [semBakeryTheory.trans_s_def]
            \\ ho_match_mp_tac RTC_TRANS
            \\ metis_tac [semBakeryTheory.trans_rules])
         \\ rw [project_def]
         \\ fs [trans_s_def]
         \\ ho_match_mp_tac RTC_TRANS
         \\ metis_tac [trans_rules]))

  >- (`trans (s,IfThen v p c c') (α,τ) (s',IfThen v p c'' c''')`
      by metis_tac [semBakeryTheory.trans_if_swap]
      \\ drule trans_imp_chorTrm
      \\ drule trans_state \\ rw []
      \\ drule Trm_trans
      \\ disch_then (qspec_then `α` drule)
      \\ rw [] \\ asm_exists_tac  \\ rw []
      \\


)






  Induct
  >- cheat (* trans_nil_false *)
  >- (rw [] \\ pop_assum (assume_tac o PURE_ONCE_REWRITE_RULE [semBakeryTheory.trans_cases])
     \\ fs []
     >- (map_every qexists_tac [`c`,`s'`]
        \\ rw [semBakeryTheory.trans_s_def,trans_s_def,project_def]
        \\ ho_match_mp_tac RTC_SINGLE
        \\ metis_tac [trans_rules])
     >- (map_every qexists_tac [`c'`,`s'`]
        \\ rw [semBakeryTheory.trans_s_def,trans_s_def,project_def]
        \\ ho_match_mp_tac RTC_SINGLE
        \\ metis_tac [trans_rules])
     >- (first_x_assum drule
        \\ first_x_assum drule
        \\ rw []
       )


  >- (`no_undefined_vars (s,c)`
      by (drule trans_state
         \\ rw [] \\ fs []
         \\ fs []
  )

trans_if_swap



Theorem preservation:
  ∀s c α τ s' c'.
   no_undefined_vars (s,c) ∧
   trans (s,c) (α,τ) (s',c')
   ⇒ ∃c'' s''. trans_s (s',c') (s'',c'')
      ∧        trans_s (s,project c) (s'',project c'')
Proof
  `∀s c α τ s' c' .
   trans (s,c) (α,τ) (s',c')
   ⇒ no_undefined_vars (s,c)
     ⇒ ∃c'' s''. trans_s (s',c') (s'',c'')
        ∧        trans_s (s,project c) (s'',project c'')`
  suffices_by metis_tac [] >>
  let
    val one2one = qmatch_goalsub_abbrev_tac `semBakery$trans_s (st,chor) _`
                  \\ map_every qexists_tac [`chor`,`st`]
                  \\ unabbrev_all_tac
                  \\ rw [trans_s_def,semBakeryTheory.trans_s_def]
                  \\ ho_match_mp_tac RTC_SINGLE
                  \\ metis_tac [trans_rules,project_def]
  in ho_match_mp_tac semBakeryTheory.trans_pairind \\ rw []
     >- one2one >- one2one >- one2one >- one2one >- one2one
  end
  (* IfThen swap *)
  >- (`no_undefined_vars (s,c) ∧ no_undefined_vars (s,c')`
      by fs [no_undefined_vars_def,free_variables_def]
      \\ first_x_assum drule
      \\ first_x_assum drule
      \\ rw []
      \\ `no_undefined_vars (s',c'') ∧ no_undefined_vars (s',c''')`
         by (rw [] \\ ho_match_mp_tac no_undefined_vars_trans_pres
            \\ metis_tac [])
      \\ `∃d. FLOOKUP s' (v,p) = SOME d ∧ FLOOKUP s (v,p) = SOME d`
         by (drule trans_state
            \\ rw [] \\ fs []
            \\ Cases_on `α`
            \\ fs [ state_from_tag_def
                  , semBakeryTheory.freeprocs_def
                  , no_undefined_vars_def
                  , free_variables_def,FLOOKUP_DEF]
            \\ EVAL_TAC
            \\ fs [])
      \\ Cases_on `d = [1w]`
      >- (map_every qexists_tac [`c''''`,`s''`]
         \\ conj_tac
         >- (fs [semBakeryTheory.trans_s_def]
            \\ ho_match_mp_tac RTC_TRANS
            \\ metis_tac [semBakeryTheory.trans_rules])
         \\ rw [project_def]
         \\ fs [trans_s_def]
         \\ ho_match_mp_tac RTC_TRANS
         \\ metis_tac [trans_rules])
      >- (map_every qexists_tac [`c'''''`,`s'''`]
         \\ conj_tac
         >- (fs [semBakeryTheory.trans_s_def]
            \\ ho_match_mp_tac RTC_TRANS
            \\ metis_tac [semBakeryTheory.trans_rules])
         \\ rw [project_def]
         \\ fs [trans_s_def]
         \\ ho_match_mp_tac RTC_TRANS
         \\ metis_tac [trans_rules]))
  >- (`no_undefined_vars (s,c)`
      by (drule trans_state
         \\ rw [] \\ fs []
         \\ fs []
  )



semBakeryTheory.trans_if_true

QED
