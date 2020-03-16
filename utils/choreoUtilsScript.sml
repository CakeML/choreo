open preamble

val _ = new_theory "choreoUtils";


Theorem RTC_TRANS = RTC_RULES |> CONV_RULE FORALL_AND_CONV
                              |> CONJUNCTS |> el 2;


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

val _ = export_theory ()
