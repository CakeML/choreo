open preamble choreoUtilsTheory chorLangTheory;

val _ = new_theory "chorLangProps";

Theorem dprocsOf_empty:
  ∀c. dprocsOf [] c = procsOf c
Proof
  ‘∀c dvars. EVERY ($= []) (MAP SND dvars) ⇒ dprocsOf dvars c = procsOf c’
    by(Induct >>
       rw[dprocsOf_def,procsOf_def] >>
       TOP_CASE_TAC >> fs[EVERY_MEM] >>
       imp_res_tac ALOOKUP_MEM >>
       fs[MEM_MAP,PULL_EXISTS] >>
       res_tac >> fs[nub'_def]) >>
  first_x_assum match_mp_tac >> simp[]
QED

Theorem procsOf_dprocsOf_SUBSET:
  ∀dvars c.
    set(procsOf c) ⊆ set(dprocsOf dvars c)
Proof
  simp[SUBSET_DEF] >>
  Induct_on ‘c’ >>
  rw[procsOf_def,dprocsOf_def,set_nub'] >>
  fs[]
QED

Theorem procsOf_dprocsOf_MEM:
  ∀proc dvars c.
    MEM proc (procsOf c) ⇒ MEM proc (dprocsOf dvars c)
Proof
  metis_tac[procsOf_dprocsOf_SUBSET,SUBSET_DEF]
QED

Theorem dprocsOf_MEM_IMP:
  ∀proc dvars c.
    MEM proc (dprocsOf dvars c) ⇒
    MEM proc (procsOf c) ∨
    ∃dn procs.
      MEM dn (dvarsOf c) ∧
      ALOOKUP dvars dn = SOME procs ∧
      MEM proc procs
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(PURE_FULL_CASE_TAC >> fs[]) >>
  metis_tac[MEM_nub']
QED

Theorem dprocsOf_ALOOKUP_EQ:
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ ALOOKUP dvars dn = ALOOKUP dvars' dn) ⇒
    dprocsOf dvars c = dprocsOf dvars' c
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(PURE_FULL_CASE_TAC >> fs[]) >>
  TRY(AP_TERM_TAC >>
      first_x_assum match_mp_tac >>
      rw[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_ALOOKUP_EQ':
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ the [] (ALOOKUP dvars dn) = the [] (ALOOKUP dvars' dn)) ⇒
    dprocsOf dvars c = dprocsOf dvars' c
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,MEM_nub',MEM_FILTER,PULL_EXISTS] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(rpt(PURE_FULL_CASE_TAC >> fs[libTheory.the_def,nub'_def]) >> NO_TAC) >>
  TRY(AP_TERM_TAC >>
      first_x_assum match_mp_tac >>
      rw[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_ALOOKUP_EQ_set:
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ set(the [] (ALOOKUP dvars dn)) = set(the [] (ALOOKUP dvars' dn))) ⇒
    set(dprocsOf dvars c) = set(dprocsOf dvars' c)
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,set_nub',MEM_FILTER,PULL_EXISTS] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM] >>
  rw[] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(last_x_assum match_mp_tac >> rw[] >> NO_TAC) >>
  TRY(rpt(PURE_FULL_CASE_TAC >> fs[libTheory.the_def,set_nub',nub'_def]) >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_ALOOKUP_EQ_set_opt:
  ∀dvars dvars' c.
    (∀dn. MEM dn (dvarsOf c) ⇒ OPTION_REL (λx y. set x = set y) (ALOOKUP dvars dn) (ALOOKUP dvars' dn)) ⇒
    set(dprocsOf dvars c) = set(dprocsOf dvars' c)
Proof
  Induct_on ‘c’ >>
  rw[dprocsOf_def,procsOf_def,dvarsOf_def,set_nub',MEM_FILTER,PULL_EXISTS] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM] >>
  rw[] >>
  res_tac >> gs[CaseEq "bool"] >>
  TRY(last_x_assum match_mp_tac >> rw[] >> NO_TAC) >>
  TRY(rpt(PURE_FULL_CASE_TAC >> fs[libTheory.the_def,set_nub',nub'_def]) >> NO_TAC) >>
  metis_tac[]
QED

Theorem dprocsOf_init_dup:
  dprocsOf ((dn,dvs)::(dn,dvs')::dvars) c = dprocsOf ((dn,dvs)::dvars) c
Proof
  match_mp_tac dprocsOf_ALOOKUP_EQ >> rw[]
QED

Theorem dprocsOf_init_swap:
  dn ≠ dn' ⇒
  dprocsOf ((dn',dvs')::(dn,dvs)::dvars) c = dprocsOf ((dn,dvs)::(dn',dvs')::dvars) c
Proof
  strip_tac >> match_mp_tac dprocsOf_ALOOKUP_EQ >> rw[]
QED

Theorem nub'_nil:
  nub' l = [] ⇔ l = []
Proof
  Cases_on ‘l’ >> rw[nub'_def]
QED

Theorem dprocsOf_dvarsOf_empty:
  ∀dvars c.
  dvarsOf c = [] ⇒
  dprocsOf dvars c = dprocsOf [] c
Proof
  rpt strip_tac >>
  match_mp_tac dprocsOf_ALOOKUP_EQ' >>
  rw[]
QED

Theorem dprocsOf_dvarsOf_empty_cons:
  ∀dvars dv c.
  dvarsOf(Fix dn c) = [] ⇒
  dprocsOf ((dn,[])::dvars) c = dprocsOf [] c
Proof
  rpt strip_tac >>
  match_mp_tac dprocsOf_ALOOKUP_EQ' >>
  rw[] >> fs[dvarsOf_def,FILTER_EQ_NIL,EVERY_MEM,MEM_nub',libTheory.the_def] >>
  res_tac >> fs[]
QED

Triviality ALOOKUP_FILTER':
  ALOOKUP (FILTER (λkv. P (FST kv)) ls) x =
  if P x then ALOOKUP ls x else NONE
Proof
  Induct_on ‘ls’ >- rw[] >>
  Cases >> rw[] >> rw[] >>
  metis_tac[]
QED

Theorem dprocsOf_nil:
  dprocsOf ((dn,[])::dvars) c = dprocsOf (FILTER ($<> dn o FST) dvars) c
Proof
  match_mp_tac dprocsOf_ALOOKUP_EQ' >> rw[ALOOKUP_FILTER',o_DEF,libTheory.the_def]
QED

Theorem nub'_procsOf:
  ∀c. nub'(procsOf c) = procsOf c
Proof
  Induct >> rw[procsOf_def,nub'_idem,nub'_FILTER] >> rw[nub'_def]
QED

Theorem nub'_dvarsOf:
  ∀c. nub'(dvarsOf c) = dvarsOf c
Proof
  Induct >> rw[dvarsOf_def,nub'_idem,nub'_FILTER] >> rw[nub'_def]
QED

Theorem nub'_dprocsOf:
  ∀c dvars. nub'(dprocsOf dvars c) = dprocsOf dvars c
Proof
  Induct >> rw[dprocsOf_def,nub'_idem,nub'_FILTER] >> rw[nub'_def]
  \\ PURE_FULL_CASE_TAC \\ gs[nub'_def,nub'_idem]
QED

Theorem dprocsOf_MEM_eq:
  MEM proc (dprocsOf dvars c) ⇔
  MEM proc (procsOf c) ∨
  ∃dn procs.
    MEM dn (dvarsOf c) ∧ ALOOKUP dvars dn = SOME procs ∧
    MEM proc procs
Proof
  rw[EQ_IMP_THM]
  >- (imp_res_tac dprocsOf_MEM_IMP >> fs[] >> metis_tac[])
  >- (drule_then MATCH_ACCEPT_TAC procsOf_dprocsOf_MEM)
  >- (rpt(pop_assum mp_tac) >>
      qid_spec_tac ‘dvars’ >>
      Induct_on ‘c’ >>
      rw[dvarsOf_def,dprocsOf_def,MEM_nub'] >>
      res_tac >> fs[] >>
      fs[MEM_FILTER,MEM_nub'])
QED

Theorem set_procsOf_dsubst_eq:
  ∀c dn c'.
    set (procsOf (dsubst c dn c')) =
    set (procsOf c) ∪
    (if MEM dn (dvarsOf c) then set (procsOf c') else {})
Proof
  Induct_on ‘c’ >> rw[procsOf_def,chorLangTheory.dsubst_def,set_nub',dvarsOf_def] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF] >>
  fs[MEM_FILTER,MEM_nub']
QED

Theorem dsubst_vacuous:
  ∀dn c c'.
  ~MEM dn (dvarsOf c) ⇒ dsubst c dn c' = c
Proof
  rpt strip_tac >> Induct_on ‘c’ >> rw[dvarsOf_def,chorLangTheory.dsubst_def,MEM_nub',MEM_FILTER]
QED

Theorem set_dvarsOf_dsubst_eq:
  ∀c dn c'.
    dvarsOf c' = [] ⇒
    set (dvarsOf (dsubst c dn c')) = (set (dvarsOf c) DIFF {dn})
Proof
  rpt strip_tac >>
  Induct_on ‘c’ >> rw[dvarsOf_def,chorLangTheory.dsubst_def,set_nub',dvarsOf_def] >>
  gs[] >>
  rw[SET_EQ_SUBSET,SUBSET_DEF,MEM_FILTER,MEM_nub'] >> fs[]
QED

Definition free_variables_def:
  (free_variables (Nil) = {}) /\
  (free_variables (Call _) = {}) /\
  (free_variables (IfThen v p c1 c2) = {(v,p)} ∪ (free_variables c1 ∪ free_variables c2)) /\
  (free_variables (Com p1 v1 p2 v2 c) = {(v1,p1)} ∪ (free_variables c DELETE (v2,p2))) /\
  (free_variables (Let v p f vl c) = set(MAP (λv. (v,p)) vl) ∪ (free_variables c DELETE (v,p))) /\
  (free_variables (Sel p b q c) = free_variables c) /\
  (free_variables (Fix x c) = free_variables c)
End

Definition defined_vars_def:
  defined_vars (s,c) = FDOM s
End

Definition no_undefined_vars_def:
  no_undefined_vars (s,c) = (free_variables c ⊆ FDOM s)
End

(* dsubst resulting free variables are bounded by the original free variables of c and c' *)
Theorem dsubst_subset_free_variables:
  ∀c c' dn.
    free_variables (dsubst c dn c') ⊆ free_variables c ∪ free_variables c'
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [free_variables_def,dsubst_def]
  \\ fs [free_variables_def,dsubst_def]
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF])
  >- (irule SUBSET_TRANS \\ asm_exists_tac \\ fs []
      \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac []
QED

(* dsubst can only add more free variables *)
Theorem free_variables_subset_dsubst:
  ∀c c' dn.
    free_variables c ⊆ free_variables (dsubst c dn c')
Proof
  rw []
  \\ Induct_on ‘c’ \\ rw [free_variables_def,dsubst_def]
  \\ fs [SUBSET_DEF]
QED

(* free_variables are the same if we are trying to substitute the same program *)
Theorem free_variables_dsubst_eq:
  ∀c dn. free_variables (dsubst c dn c) = free_variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [free_variables_subset_dsubst,
                dsubst_subset_free_variables,
                UNION_IDEMPOT]
QED

(* free_variables are the same if we are trying to substitute the same program *)
Theorem free_variables_dsubst_eq_Fix:
  ∀c x y. free_variables (dsubst c x (Fix y c)) = free_variables c
Proof
  rw [] \\ irule SUBSET_ANTISYM
  \\ metis_tac [free_variables_subset_dsubst,
                dsubst_subset_free_variables,
                free_variables_def,
                UNION_IDEMPOT]
QED

(* If there are no undefined variables no lookup into
   the state should fail (give NONE)
*)
Theorem no_undefined_FLOOKUP:
  (∀p v s c q x. no_undefined_vars (s,Com p v q x c)
    ⇒ ∃x. FLOOKUP s (v,p) = SOME x)
∧ (∀p v s c c1 c2. no_undefined_vars (s,IfThen v p c1 c2)
    ⇒ ∃x. FLOOKUP s (v,p) = SOME x)
∧ (∀p l s c v f. no_undefined_vars (s,Let v p f l c)
    ⇒ EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) l)))
Proof
  rw [no_undefined_vars_def,free_variables_def,FDOM_FLOOKUP]
  \\ Induct_on ‘l’ \\ fs [] \\ rw [FDOM_FLOOKUP] \\ rw [IS_SOME_DEF]
QED

(* MP-friendly version of no_undefined_FLOOKUP *)
val t_list = no_undefined_FLOOKUP |> CONJUNCTS

Theorem no_undefined_FLOOKUP_if  = el 2 t_list
Theorem no_undefined_FLOOKUP_com = el 1 t_list
Theorem no_undefined_FLOOKUP_let = el 3 t_list

(* Ensure no self communication of a choreography *)
Definition no_self_comunication_def:
  no_self_comunication (Com p _ q _ c)   = (p ≠ q ∧ no_self_comunication c)
∧ no_self_comunication (Sel p _ q c)     = (p ≠ q ∧ no_self_comunication c)
∧ no_self_comunication (IfThen _ _ c c') = (no_self_comunication c ∧
                                            no_self_comunication c')
∧ no_self_comunication (Let _ _ _ _ c)   = no_self_comunication c
∧ no_self_comunication (Fix _ c)         = no_self_comunication c
∧ no_self_comunication _                 = T
End

Theorem no_self_comunication_dsubst:
  ∀c c' dn.
    no_self_comunication c ∧ no_self_comunication c'
    ⇒ no_self_comunication (dsubst c dn c')
Proof
  rw [] \\ Induct_on ‘c’
  \\ rw [no_self_comunication_def,dsubst_def]
  \\ fs [no_self_comunication_def,dsubst_def]
QED



val _ = export_theory ()
