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

val _ = export_theory ()
