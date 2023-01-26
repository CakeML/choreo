open preamble

val _ = new_theory "choreoUtils";


Theorem RTC_TRANS = RTC_RULES |> CONV_RULE FORALL_AND_CONV
                              |> CONJUNCTS |> el 2;

Theorem RTC_SANDWICH:
  !R a b c d. R^* a b /\ R b c /\ R^* c d ==> R^* a d
Proof
  metis_tac[RTC_RTC,RTC_SINGLE]
QED

Theorem RTC_SPLIT:
  ∀R x y z. R^* x z ∧ R^* z y ⇒ R^* x y
Proof
  metis_tac[RTC_RTC,RTC_SINGLE]
QED

Theorem INDEX_FIND_normalize:
  !l n. OPTION_MAP SND (INDEX_FIND n f l) = OPTION_MAP SND (INDEX_FIND 0 f l)
Proof
  Induct_on `l` >> rpt strip_tac >> rw[INDEX_FIND_def]
QED

Theorem INDEX_FIND_normalize':
  !l n. (INDEX_FIND n f l = NONE) = (INDEX_FIND 0 f l = NONE)
Proof
  Induct_on `l` >> rpt strip_tac >> rw[INDEX_FIND_def]
QED

Theorem INDEX_FIND_normalize'':
  !n f l z. (INDEX_FIND (SUC n) f l = SOME z) = (FST z > 0 /\ INDEX_FIND n f l = SOME (FST z - 1, SND z))
Proof
  Induct_on `l` >> rpt strip_tac
  >> rw[INDEX_FIND_def,EQ_IMP_THM]
  >> fs[] >> Cases_on `z` >> fs[]
QED

Theorem FIND_APPEND:
   FIND f (l1 ++ l2) =
   case FIND f l1 of NONE => FIND f l2
      | SOME e => SOME e
Proof
  Induct_on `l1` >> fs[FIND_def,INDEX_FIND_def]
  >> rw[INDEX_FIND_normalize]
QED

Theorem FIND_NOT_MEM:
  !e l. FIND ($= e) l = NONE <=> ¬MEM e l
Proof
  Induct_on `l` >> rw[FIND_def,INDEX_FIND_def] >> fs[FIND_def,INDEX_FIND_normalize']
QED

Theorem FIND_o_NOT_MEM:
  !e f l. FIND ($= e o f) l = NONE <=> ¬MEM e (MAP f l)
Proof
  Induct_on `l` >> rw[FIND_def,INDEX_FIND_def] >> fs[FIND_def,INDEX_FIND_normalize']
QED

Theorem FIND_o_MEM:
  !e f l. FIND ($= e o f) l <> NONE <=> MEM e (MAP f l)
Proof
  Induct_on `l` >> rw[FIND_def,INDEX_FIND_def] >> fs[FIND_def,INDEX_FIND_normalize']
QED

Theorem FIND_MEM:
  !f l z. FIND f l = SOME z
  ==> MEM z l /\ f z
Proof
  Induct_on `l` >> rpt strip_tac
  >> fs[FIND_def,INDEX_FIND_def] >> every_case_tac
  >> rveq >> fs[INDEX_FIND_normalize'' |> Q.SPEC `0` |> REWRITE_RULE [GSYM ONE]]
  >> metis_tac[FST,SND]
QED

(* Alternative version of nub that keeps elements at the
   head of the list
*)
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

(* lists produced by nub' are ALL_DISTINCT *)
Theorem all_distinct_nub':
  ∀l. ALL_DISTINCT (nub' l)
Proof
  rw [ALL_DISTINCT,nub'_def]
  \\ Induct_on `l`
  \\ rw [ALL_DISTINCT,nub'_def,FILTER_ALL_DISTINCT,MEM_FILTER]
QED

(* nub' preserves membership *)
Theorem MEM_nub':
  ∀l x. MEM x (nub' l) = MEM x l
Proof
  Induct
  \\ rw [nub'_def]
  \\ Cases_on ‘x=h’ \\ fs [MEM_FILTER]
QED

Theorem set_nub':
  ∀e. set(nub' e) = set e
Proof
  rw[FUN_EQ_THM] >>
  simp[MEM_nub' |> SIMP_RULE std_ss [IN_DEF]]
QED

Theorem ALOOKUP_SOME_SPLIT:
  ∀l x y. ALOOKUP l x = SOME y ⇔ ∃l1 l2. l = l1 ++ (x,y)::l2 ∧ ~MEM x (MAP FST l1)
Proof
  ho_match_mp_tac ALOOKUP_ind >>
  rw[EQ_IMP_THM]
  >- (qexists_tac ‘[]’ >> simp[])
  >- (fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[])
  >- (res_tac >>
      rveq >>
      Q.REFINE_EXISTS_TAC ‘(_,_)::_’ >> simp[])
  >- (fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
      rveq >> fs[] >>
      fs[ALOOKUP_APPEND,CaseEq "option"] >>
      fs[ALOOKUP_NONE])
QED

Theorem LIST_REL_MEM_IMP_SYM:
  ∀xs ys P y. LIST_REL P xs ys ∧ MEM y ys ⇒ ∃x. MEM x xs ∧ P x y
Proof
  rw[] >>
  drule_at (Pos last) EVERY2_sym >>
  disch_then(qspec_then ‘λ y x. P x y’ mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  imp_res_tac LIST_REL_MEM_IMP >>
  metis_tac[]
QED

Theorem DIFF_UNION':
  (x ∪ y) DIFF z = (x DIFF z) ∪ (y DIFF z)
Proof
  rw[SET_EQ_SUBSET,SUBSET_DEF]
QED

Theorem nub'_APPEND:
  nub'(xs ++ ys) = nub' xs ++ FILTER (λy. ~MEM y xs) (nub' ys)
Proof
  Induct_on ‘xs’ >> fs[nub'_def,FILTER_APPEND,FILTER_FILTER] >>
  strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> rw[FUN_EQ_THM,EQ_IMP_THM]
QED

Theorem ALOOKUP_REVERSE_ALL_DISTINCT:
  ALL_DISTINCT (MAP FST l) ⇒
  ALOOKUP (REVERSE l) = ALOOKUP l
Proof
  strip_tac >>
  match_mp_tac ALOOKUP_ALL_DISTINCT_PERM_same >>
  fs[MAP_REVERSE]
QED

Theorem PAIR_MAP_app:
  (f ## g) = (λ(x,y). (f x,g y))
Proof
  rw[FUN_EQ_THM] >>
  pairarg_tac >> rw[]
QED

Theorem ALOOKUP_LIST_REL_lemma:
  ∀R l1 l2 x y.
  MAP FST l1 = MAP FST l2 ∧
  LIST_REL R (MAP SND l1) (MAP SND l2) ∧
  ALOOKUP l1 x = SOME y ⇒
  ∃z. ALOOKUP l2 x = SOME z ∧ R y z
Proof
  strip_tac >>
  Induct >- fs[] >>
  Cases >> Cases >- rw[] >>
  rw[] >>
  qmatch_goalsub_abbrev_tac ‘pair::_’ >> Cases_on ‘pair’ >> fs[]
QED

Theorem ALOOKUP_LIST_REL_lemma':
  ∀R l1 l2 x y.
  LIST_REL (λ(dn,cls) (dn',cls'). dn = dn' ∧ R dn cls cls') l1 l2 ∧
  ALOOKUP l1 x = SOME y ⇒
  ∃z. ALOOKUP l2 x = SOME z ∧ R x y z
Proof
  strip_tac >>
  Induct >- fs[] >>
  Cases >> Cases >- rw[] >>
  rw[] >>
  qmatch_goalsub_abbrev_tac ‘pair::_’ >> Cases_on ‘pair’ >> fs[] >>
  rveq >> fs[]
QED

Theorem nub'_FILTER:
  ∀P l. nub'(FILTER P l) = FILTER P (nub' l)
Proof
  Induct_on ‘l’ >> rw[nub'_def,FILTER_FILTER] >>
  simp[CONJ_SYM] >>
  rw[FILTER_EQ,EQ_IMP_THM]
QED

Theorem nub'_idem:
  ∀l. nub'(nub' l) = nub' l
Proof
  Induct >>
  rw[nub'_def,nub'_FILTER,FILTER_FILTER]
QED

(* Project a global state `(proc,var) |-> val` into a single process
   state `var |-> val`
*)
Definition projectS_def:
  projectS p s = MAP_KEYS (λx. FST x) (DRESTRICT s (λx. SND x = p))
End

(* The domain of a state `s` projected to a process `p` is the set of
   all variable names associated with `p` in the domain of `s`
*)
Theorem fdom_projectS:
  ∀p s. FDOM (projectS p s) = { v | (v,p) ∈ FDOM s }
Proof
  rw [projectS_def,MAP_KEYS_def,DRESTRICT_DEF,IMAGE_DEF,FUN_EQ_THM]
  \\ EQ_TAC >> rw [] >> fs [] >> Q.EXISTS_TAC `(x,p)` >> rw []
QED


(* If a key `(v,p)` is in the domain of a global state `s` then
   one can expect the application of the projected key `v` over
   a projected state `projectS p s` to be equal to an original
   (un-projected) application
*)
Theorem fapply_projectS:
  ∀p v (s : β # α |-> γ). (v,p) ∈ FDOM s ⇒ projectS p s ' v = s ' (v,p)
Proof
  rw [projectS_def,MAP_KEYS_def,DRESTRICT_DEF]
  \\ sg `INJ FST (FDOM (DRESTRICT s (λx. SND x = p))) 𝕌(:β)`
  >- rw [DRESTRICT_DEF,INJ_DEF,PAIR_FST_SND_EQ]
  \\ IMP_RES_TAC (MAP_KEYS_def |> CONV_RULE (TOP_DEPTH_CONV FORALL_AND_CONV) |> CONJUNCT2)
  \\ first_x_assum (ASSUME_TAC o Q.SPEC `(v,p)`)
  \\ rfs [DRESTRICT_DEF,ETA_THM]
QED

(* If a value is available on a state `s` with key `(v,p)` then it
   should also be available in a projected state `projectS p s` with
   key `v`
*)
Theorem lookup_projectS:
  ∀p v s d. FLOOKUP s (v,p) = SOME d ⇒ FLOOKUP (projectS p s) v = SOME d
Proof
  rw [FLOOKUP_DEF,fapply_projectS,fdom_projectS]
QED

(* Alternative version of lookup_projectS *)
Theorem lookup_projectS':
  ∀p v s d. FLOOKUP s (v,p) = FLOOKUP (projectS p s) v
Proof
  rw [FLOOKUP_DEF,fapply_projectS,fdom_projectS]
QED

(* If a state is updated with bindings for a process (`p2`) this does not
   affect the projection of any other process (`p1`)
*)
Theorem fupdate_projectS:
  ∀p1 p2 s v d. p1 ≠ p2 ⇒ projectS p1 (s |+ ((v,p2),d)) = projectS p1 s
Proof
  rw [projectS_def]
QED

(*  Updating a projected state is equivalent to updating
    a global state with the corresponding process

*)
Theorem projectS_fupdate:
  ∀p v d s. projectS p (s |+ ((v,p),d)) = projectS p s |+ (v,d)
Proof
  rw [projectS_def]
  \\ sg `INJ FST ((v,p) INSERT FDOM (DRESTRICT s (λx. SND x = p))) 𝕌(:β)`
  >- REPEAT (rw [DRESTRICT_DEF,INJ_DEF,PAIR_FST_SND_EQ])
  \\ IMP_RES_TAC (MAP_KEYS_FUPDATE)
  \\ first_x_assum (ASSUME_TAC o Q.SPEC `d`)
  \\ rfs [DRESTRICT_DEF,ETA_THM]
QED

val _ = export_theory ()
