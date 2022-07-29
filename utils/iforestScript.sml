open HolKernel Parse boolLib bossLib preamble;
open llistTheory optionTheory itreesTheory finite_mapTheory;

val _ = new_theory "iforest";

(* iforest abstract definition *)

Datatype:
  itree_action = Ext 'a | Int | Res 'r
End

Datatype:
  iforest = <| forest : 'p |-> ('a,'e,'r) itree ;
               st     : 's;
               act    : 's -> 'p -> 'e -> 'a option;
               upd    : 's -> 'p -> 'e -> 's;
            |>
End

val iforest = “ψ  :('a,'e,'p,'r,'s) iforest”
val psi     = “ψ  :('a,'e,'p,'r,'s) iforest”
val psi'    = “ψ' :('a,'e,'p,'r,'s) iforest”

(* iforest basic operations *)

Definition iforest_get_def:
  iforest_get ^iforest p = FLOOKUP ψ.forest p
End

Definition iforest_set_def:
  iforest_set ^iforest p i = ψ with forest := ψ.forest |+ (p,i)
End

Definition iforest_del_def:
  iforest_del ^iforest p = ψ with forest := ψ.forest \\ p
End

Definition iforest_upd_act_def:
  iforest_upd_act ^iforest p e = ψ with st := ψ.upd ψ.st p e
End

Definition iforest_upd_def:
  iforest_upd ^iforest p e f =
    case ψ.act ψ.st p e of
      NONE   => ψ
    | SOME a => ψ with <| forest := ψ.forest |+ (p,f a); st := ψ.upd ψ.st p e |>
End

Theorem iforest_upd_alt_def:
∀ψ p e f.
  IS_SOME (ψ.act ψ.st p e) ⇒
  iforest_upd ψ p e f = iforest_upd_act (iforest_set ψ p (f (THE (ψ.act ψ.st p e)))) p e
Proof
  rw[iforest_upd_def,iforest_set_def,iforest_upd_act_def,IS_SOME_EXISTS]
  \\ simp[]
QED

Definition iforest_itrees_def:
  iforest_itrees ^iforest = FDOM ψ.forest
End

Definition iforest_can_act_def:
  iforest_can_act ^iforest p =
  case iforest_get ψ p of
    NONE => F
  | SOME (Vis e f) => IS_SOME (ψ.act ψ.st p e)
  | _ => T
End

(* A trace is a stream of Itree identifiers to operate over.
   It is meant to represent in which order the forest is being
   evaluated. For most useful proofs about a forest some notion
   of fair trace might be needed.
*)
val trace   = “trace   : 'p llist”
val trace'  = “trace'  : 'p llist”

Definition next_proc_def:
  next_proc ^iforest [||]  = NONE
∧ next_proc ^iforest (x:::xs) =
    case LFILTER (iforest_can_act ψ) (x:::xs) of
      [||] => NONE
    | p:::ll => SOME (p,xs)
End

(* Properties of the basic iforest operations *)

Theorem next_proc_ifores_get_SOME:
  ∀ψ trace p ll.
    next_proc ψ trace = SOME (p,ll)
    ⇒ ∃i. iforest_get ψ p = SOME i
Proof
  Cases_on ‘trace’ \\ rw[next_proc_def]
  >- (gs[iforest_can_act_def]
      \\ Cases_on ‘iforest_get ψ h’
      \\ gs[])
  \\ gs[CaseEq"llist"]
  \\ drule LFILTER_EQ_CONS
  \\ rw[iforest_can_act_def]
  \\ Cases_on ‘iforest_get ψ p’
  \\ gs[]
QED

Theorem iforest_can_act_in_itrees:
  ∀ψ p. iforest_can_act ψ p ⇒ p ∈ iforest_itrees ψ
Proof
  rw[iforest_itrees_def,FDOM_FLOOKUP,iforest_can_act_def,iforest_get_def]
  \\ EVERY_CASE_TAC \\ gs[]
QED

Theorem iforest_itrees_del:
  ∀ψ p.
    p ∉ iforest_itrees (iforest_del ψ p)
Proof
  simp[iforest_del_def,iforest_itrees_def]
QED

Definition iforest_step_def:
  (* If the Itree is done, remove it from the forest *)
  iforest_step ψ p (Ret t)   = iforest_del ψ p
  (* If the Itree is in an internal transition simply update it *)
∧ iforest_step ψ p (Tau t)   = iforest_set ψ p t
  (* If the Itree returns an event:  *)
  (* We must likely can act on it (from next_proc)  *)
  (* So, we update the act function according to upd
        and record the event to the stream. *)
∧ iforest_step ψ p (Vis e f) = iforest_upd ψ p e f
End

Definition iforest_act_def:
  iforest_act ψ p (Ret t)   = (p,Res t)
∧ iforest_act ψ p (Tau t)   = (p,Int)
∧ iforest_act ψ p (Vis e f) = (p,Ext e)
End

Theorem iforest_act_FST:
  ∀ψ p i. FST (iforest_act ψ p i) = p
Proof
  Cases_on ‘i’ \\ gs[iforest_act_def]
QED

(* Folding function to be used with  LUNFOLD *)
Definition iforest_aux1_def:
  iforest_aux (^iforest,^trace) =
  case next_proc ψ trace of
    NONE => NONE
  | SOME (p,ll) =>
      case iforest_get ψ p of
        NONE   => NONE
      | SOME i => SOME ((iforest_step ψ p i,ll),iforest_act ψ p i)
End

(* To create the stream of events we filter out all the NONE element from
   Ret and Tau Itrees
*)
Definition iforest_aux_def:
  iforest ^iforest ^trace =
    LUNFOLD iforest_aux (ψ,trace)
End

(* Much nicer version of iforest.
   - Comments are duplicated from iforest_aux1_def
 *)
Theorem iforest_def[compute]:
∀ ^iforest ^trace.
  iforest ^iforest ^trace =
  case next_proc ψ trace of
    NONE => [||]
  | SOME (p,ll) =>
      let i = THE (iforest_get ψ p)
      in iforest_act ψ p i ::: iforest (iforest_step ψ p i) ll
Proof
  rw[iforest_aux_def,Once iforest_aux1_def,Once LUNFOLD]
  \\ Cases_on ‘next_proc ψ trace’ \\ gs[]
  \\ Cases_on ‘x’ \\ gs[]
  \\ drule next_proc_ifores_get_SOME \\ rw[]
  \\ simp[]
QED

Theorem iforest_alt_def:
∀ ^iforest ^trace.
  iforest ^iforest ^trace =
  case next_proc ψ trace of
    NONE => [||]
  | SOME (p,ll) =>
      case iforest_get ψ p of
        NONE => [||]
      | SOME i => iforest_act ψ p i ::: iforest (iforest_step ψ p i) ll
Proof
  rw[iforest_aux_def,Once iforest_aux1_def,Once LUNFOLD]
  \\ Cases_on ‘next_proc ψ trace’ \\ gs[]
  \\ Cases_on ‘x’ \\ gs[]
  \\ drule next_proc_ifores_get_SOME \\ rw[]
  \\ simp[]
QED

Theorem iforest_eq:
  ∀R ^iforest ^trace res.
    R ψ trace res ∧
    (∀^iforest ^trace res.
      R ψ trace res ⇒
        (IS_NONE (next_proc ψ trace) ∧ res = [||]) ∨
        (∃p ll i res'.
           next_proc ψ trace = SOME (p,ll) ∧
           iforest_get ψ p = SOME i ∧
           res = iforest_act ψ p i:::res' ∧
           R (iforest_step ψ p i) ll res')) ⇒
    (iforest ψ trace = res)
Proof
  rw[]
  \\ rw[Once LLIST_BISIMULATION]
  \\ qexists_tac
     ‘λll1 ll2.
        ∃^iforest trace.
          ll1 = iforest ψ trace ∧ R ψ trace ll2’
  \\ rw[]
  >- metis_tac []
  \\ res_tac \\ rw[]
  \\ gs[Once iforest_def]
  \\ metis_tac []
QED

Theorem iforest_itrees_mono_step:
  ∀i ψ p. p ∈ iforest_itrees ψ ⇒ iforest_itrees (iforest_step ψ p i) ⊆ iforest_itrees ψ
Proof
  rw[] \\ Cases_on ‘i’ \\ EVAL_TAC
  \\ gs[FDOM_DRESTRICT,iforest_itrees_def]
  \\ Cases_on ‘ψ.act ψ.st p a’ \\ gs[]
QED

Theorem next_proc_SOME:
  ∀ψ trace p r.
  next_proc ψ trace = SOME (p,r)
  ⇒ r = THE (LTL trace) ∧ ∃ll. LFILTER (iforest_can_act ψ) trace = p:::ll
Proof
  rw[] \\ Cases_on ‘trace’
  >- gs[next_proc_def]
  >- (pop_assum mp_tac \\ ONCE_REWRITE_TAC [next_proc_def]
      \\ CASE_TAC \\ drule LFILTER_EQ_CONS \\ rw[])
  >- gs[next_proc_def]
  >- (pop_assum mp_tac \\ ONCE_REWRITE_TAC [next_proc_def]
      \\ CASE_TAC \\ drule LFILTER_EQ_CONS \\ rw[])
QED

Theorem not_in_forest_not_in_trace:
  ∀p ^psi trace.
    p ∉ iforest_itrees ψ
    ⇒ every (λ(q,a). p ≠ q) (iforest ψ trace)
Proof
  rw[]
  \\ ho_match_mp_tac (MP_CANON every_strong_coind)
  \\ qexists_tac ‘λll. ∃^psi' trace. ll = iforest ψ' trace ∧  iforest_itrees ψ' ⊆ iforest_itrees ψ’
  \\ rw[]
  >- (Cases_on ‘h’ \\ rw[] \\ gs[Once iforest_def]
      \\ Cases_on ‘next_proc ψ' trace’ \\ gs[]
      \\ Cases_on ‘x’ \\ gs[] \\ rveq
      \\ first_x_assum (assume_tac o Q.AP_TERM ‘FST’)
      \\ gs[iforest_act_FST] \\ rveq
      \\ ‘p ∉ iforest_itrees ψ'’
         by (gs[SUBSET_DEF] \\ CCONTR_TAC \\ gs[])
      \\ drule next_proc_SOME \\ rw[]
      \\ drule LFILTER_EQ_CONS
      \\ rw[] \\ CCONTR_TAC \\ gs [iforest_can_act_in_itrees])
  >- (Cases_on ‘h’ \\ rw[] \\ gs[Once iforest_def]
      \\ Cases_on ‘next_proc ψ' trace’ \\ gs[]
      \\ Cases_on ‘x’ \\ gs[] \\ rveq
      \\ disj1_tac \\ qexists_tac ‘iforest_step ψ' q' (THE (iforest_get ψ' q'))’
      \\ qexists_tac ‘r'’ \\ simp[]
      \\ irule SUBSET_TRANS \\ first_x_assum (irule_at Any) \\ simp[]
      \\ irule iforest_itrees_mono_step
      \\ drule next_proc_SOME \\ rw[]
      \\ drule LFILTER_EQ_CONS \\ rw[]
      \\ rw[iforest_can_act_in_itrees])
  >- (qexists_tac ‘ψ’ \\ simp[] \\ metis_tac [])
QED

Theorem iforest_not_in_forest:
  ∀n ^iforest trace p a.
    p ∉ iforest_itrees ψ
    ⇒ LNTH n (iforest ψ trace) ≠ SOME (p,a)
Proof
  rw[] \\ drule not_in_forest_not_in_trace
  \\ disch_then (qspec_then ‘trace’ assume_tac)
  \\ gs[every_LNTH]
  \\ Cases_on ‘LNTH n (iforest ψ trace)’ \\ gs[]
  \\ first_x_assum drule \\ Cases_on ‘x’ \\ simp[]
QED


Theorem iforest_cons_cases:
  ∀ψ trace x xs.
    iforest ψ trace = x:::xs
    ⇒ ∃p ll. next_proc ψ trace = SOME (p,ll) ∧
             ((∃t. x = (p,Res t)   ∧ xs = iforest (iforest_del ψ p) ll) ∨
              (∃t. x = (p,Int)     ∧ xs = iforest (iforest_set ψ p t) ll) ∨
              (∃e f. x = (p,Ext e) ∧ xs = iforest (iforest_upd ψ p e f) ll))
Proof
  rw[Once iforest_def]
  \\ Cases_on ‘next_proc ψ trace’ \\ gs[]
  \\ Cases_on ‘x'’ \\ gs[]
  \\ drule next_proc_ifores_get_SOME
  \\ strip_tac \\ gs[]
  \\ Cases_on ‘i’ \\ gs[iforest_step_def,iforest_act_def]
  \\ metis_tac []
QED

Theorem iforest_nth_drop:
  ∀n ^psi trace p a.
    LNTH n (iforest ψ trace) = SOME (p,a)
    ⇒ ∃^psi' trace' i.
        iforest_get ψ' p = SOME i ∧
        iforest_act ψ' p i = (p,a) ∧
        LDROP n (iforest ψ trace) = SOME ((p,a) ::: iforest (iforest_step ψ' p i) trace')
Proof
  Induct \\ rw[]
  >- (Cases_on ‘iforest ψ trace’ \\ gs[LNTH]
      \\ pop_assum (assume_tac o ONCE_REWRITE_RULE [iforest_def])
      \\ Cases_on ‘next_proc ψ trace’ \\ gs[]
      \\ Cases_on ‘x’ \\ gs[]
      \\ drule next_proc_ifores_get_SOME
      \\ strip_tac \\ gs[]
      \\ ‘q = p’ by
        (first_assum (assume_tac o Q.AP_TERM ‘FST’)
         \\ gs[iforest_act_FST])
      \\ rveq
      \\ metis_tac [])
  \\ gs[LNTH,OPTION_JOIN_EQ_SOME]
  \\ pop_assum (assume_tac o GSYM)
  \\ Cases_on ‘iforest ψ trace’
  \\ gs[] \\ rveq
  \\ drule iforest_cons_cases
  \\ rw[]
  \\ metis_tac []
QED

(* A trace of actions which stop producing actions for a process after
   it reaches a Res(ult)
 *)
Definition actions_end_def:
  actions_end actions =
  ∀n m p t a.
    LNTH n actions = SOME (p, Res t) ∧ n < m ⇒
    LNTH m actions ≠ SOME (p, a)
End

(* If an itree returns in the forest it never does any more actions *)
Theorem iforest_actions_end_aux[local]:
  ∀n m ψ trace p t a.
    LNTH n (iforest ψ trace) = SOME (p, Res t) ⇒
      LNTH (n + SUC m) (iforest ψ trace) ≠ SOME (p,a)
Proof
  rw[] \\ drule iforest_nth_drop \\ rw[]
  \\ simp[LNTH_ADD]
  \\ Cases_on ‘i’ \\ gs[iforest_act_def] \\ rveq
  \\ gs[iforest_step_def]
  \\ irule iforest_not_in_forest
  \\ simp[iforest_itrees_del]
QED

Theorem actions_end_iforest:
  ∀ψ trace. actions_end (iforest ψ trace)
Proof
  rw[actions_end_def]
  \\ drule iforest_actions_end_aux \\ rw[]
  \\ drule LESS_STRONG_ADD \\ rw[]
  \\ metis_tac []
QED

Definition fair_trace_def:
  fair_trace procs trace =
    ∀p. p ∈ procs ⇒ always (λll. ∃n. LNTH n ll = SOME p) trace
End

Theorem LNTH_exists_LDROP:
  ∀n l p.
    LNTH n l = SOME p
    ⇒ ∃ll. LDROP n l = SOME (p:::ll)
Proof
  Induct \\ rw[]
  >- (Cases_on ‘l’ \\ gs[])
  \\ gs[LNTH]
  \\ Cases_on ‘l’ \\ gs[]
QED

Theorem fair_trace_ldrop_rec:
  ∀procs trace p.
    fair_trace procs trace ∧ p ∈ procs ⇒
      ∃n ll. LDROP n trace = SOME (p ::: ll) ∧ fair_trace procs ll
Proof
  rw[fair_trace_def]
  \\ cases_on ‘trace’ \\ gs[always_thm]
  \\ first_assum drule \\ strip_tac
  \\ drule LNTH_LDROP  \\ rw[] \\ gs[]
  \\ qexists_tac ‘n’
  \\ Induct_on ‘n’ \\ rw[]
  \\ drule LNTH_exists_LDROP
  \\ rw[] \\ gs[] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ drule always_DROP
  \\ disch_then (qspec_then ‘n’ assume_tac)
  \\ gs[]
QED

Theorem always_infinite:
  ∀P l.
    ¬ P [||] ∧ always P l
    ⇒ ¬ LFINITE l
Proof
  rw[LFINITE_LNTH_NONE]
  \\ ‘∃x. LNTH n l = SOME x’ by
    (pop_assum mp_tac
     \\ qid_spec_tac ‘l’
     \\ Induct_on ‘n’ \\ rw[]
     >- gs[Once always_cases]
     \\ pop_assum mp_tac
     \\ simp[Once always_cases]
     \\ rw[] \\ rw[LNTH_THM])
  \\ gs[]
QED

Theorem LDROP_APPEN_fromList:
  ∀l ll.
    LDROP (LENGTH l) (LAPPEND (fromList l) ll) = SOME ll
Proof
  rw[] \\ Induct_on ‘l’ \\ rw[]
QED

Theorem fair_trace_inifite_proc:
  ∀procs trace p.
    fair_trace procs trace ∧ p ∈ procs ⇒
    ¬ LFINITE (LFILTER (λq. p = q) trace)
Proof
  rw[fair_trace_def,LFINITE_LNTH_NONE]
  \\ first_x_assum drule \\ rw[]
  \\ ‘∃x. LNTH n (LFILTER (λq. p = q) trace) = SOME x’
    by (pop_assum mp_tac
        \\ qid_spec_tac ‘trace’
        \\ induct_on ‘n’ \\ rw[LNTH_THM]
        >- (Cases_on ‘LFILTER (λq. p = q) trace’ \\ simp[LNTH_THM]
            \\ gs[LFILTER_EQ_NIL,every_def]
            \\ pop_assum mp_tac \\ simp[]
            \\ gs[Once always_cases]
            \\ Cases_on ‘n’ \\ gs[]
            \\ disj2_tac \\ gs[exists_LNTH]
            \\ metis_tac [])
        >- (Cases_on ‘LFILTER (λq. p = q) trace’ \\ simp[LNTH_THM]
            >- (gs[LFILTER_EQ_NIL,every_def]
                \\ pop_assum mp_tac \\ simp[]
                \\ pop_assum mp_tac \\ simp[Once always_cases]
                \\ rw[] \\ Cases_on ‘n'’ \\ gs[]
                \\ disj2_tac \\ gs[exists_LNTH]
                \\ metis_tac [])
            >- (drule LFILTER_EQ_CONS \\ rw[]
                \\ drule always_DROP
                \\ disch_then (qspec_then ‘LENGTH l’ assume_tac)
                \\ first_x_assum irule
                \\ gs[LDROP_APPEN_fromList])))
       \\ gs[]
QED

(* Weak deadlock-freedom states that either the trace of actions goes forever or
   or that every process reaches a result state
 *)
Definition weak_deadlock_freedom_def:
  weak_deadlock_freedom procs actions =
    (actions_end actions ∧
    (¬ LFINITE actions ∨ ∀p. p ∈ procs ⇒ exists (λ(q,a). p = q ∧ ∃t. a = Res t) actions))
End

Definition strong_deadlock_freedom_def:
  strong_deadlock_freedom procs actions =
    (actions_end actions ∧
     ∀p. p ∈ procs ⇒
         exists (λ(q,a). p = q ∧ ∃t. a = Res t) actions ∨
         always (λll. ∃n a. LNTH n ll = SOME (p,a)) actions)
End

Theorem iforest_itrees_iforest_step_in:
  ∀p ψ q i.
    p ∈ iforest_itrees ψ ∧ p ≠ q
    ⇒ p ∈ iforest_itrees (iforest_step ψ q i)
Proof
  rw[]
  \\ Cases_on ‘i’
  \\ gs[iforest_step_def,iforest_del_def,iforest_set_def,iforest_upd_def,iforest_itrees_def]
  \\ TOP_CASE_TAC \\ gs[]
QED

Theorem iforest_itrees_iforest_step_mono:
  ∀p ψ q i.
    p ∈ iforest_itrees ψ ∧ (∀t. i ≠ Ret t)
    ⇒ p ∈ iforest_itrees (iforest_step ψ p i)
Proof
  rw[]
  \\ Cases_on ‘i’ \\ gs[]
  \\ gs[iforest_step_def,iforest_del_def,iforest_set_def,iforest_upd_def,iforest_itrees_def]
  \\ TOP_CASE_TAC \\ gs[]
QED

Theorem iforest_itrees_FEMPTY:
  ∀p ψ.
    ψ.forest = FEMPTY ⇒ p ∉ iforest_itrees ψ
Proof
  rw[iforest_itrees_def]
QED

Theorem weak_deadlock_freedom_iforest_coind:
  ∀R.
    (∀ψ trace.
       R ψ trace ⇒
       ψ.forest = FEMPTY ∨
       (∃p ll i.
          next_proc ψ trace = SOME (p,ll) ∧
          iforest_get ψ p = SOME i ∧
          R  (iforest_step ψ p i) ll)) ⇒
  ∀ψ trace. R ψ trace
      ⇒ weak_deadlock_freedom (iforest_itrees ψ) (iforest ψ trace)
Proof
  rw[weak_deadlock_freedom_def,actions_end_iforest]
  \\ Cases_on ‘LFINITE (iforest ψ trace)’ \\ gs[]
  \\ last_x_assum mp_tac  \\ last_x_assum mp_tac
  \\ qabbrev_tac ‘actions = iforest ψ trace’
  \\ ‘actions = iforest ψ trace’ by gs[Abbr‘actions’]
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘ψ’,‘trace’]
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘actions’
  \\ ho_match_mp_tac LFINITE_STRONG_INDUCTION
  \\ rw[]
  >- (first_x_assum drule \\ rw[]
      \\ gs[Once iforest_def,iforest_itrees_FEMPTY])
  \\ first_assum drule \\ strip_tac
  >- gs[iforest_itrees_FEMPTY]
  \\ qpat_x_assum ‘h:::actions = _’ mp_tac
  \\ simp[Once iforest_def] \\ rw[]
  \\ gs[AND_IMP_INTRO]
  \\ first_x_assum (drule_at_then Any kall_tac)
  \\ last_x_assum (drule_at Any) \\ rw[]
  \\ Cases_on ‘p = p'’ \\ gs[]
  >- (rveq \\ Cases_on ‘∃t. i = Ret t’ \\ gs[iforest_act_def]
      \\ disj2_tac \\ first_x_assum irule
      \\ irule iforest_itrees_iforest_step_mono \\ rw[])
  \\ disj2_tac \\ first_x_assum irule
  \\ metis_tac [iforest_itrees_iforest_step_in]
QED

Inductive rooted:
[~can_act:]
  (∀ψ p. iforest_can_act ψ p  ⇒ rooted ψ p) ∧
[~one_step:]
  (∀ψ p q i.
     ¬iforest_can_act ψ p ∧
     (* Need this or rooted becomes a tautology *)
     iforest_can_act ψ q ∧
     iforest_get ψ q = SOME i ∧
     rooted (iforest_step ψ p i) p
     ⇒ rooted ψ p)
End

Definition all_rooted_def:
  all_rooted ψ = ∀p. p ∈ iforest_itrees ψ ⇒ rooted ψ p
End

CoInductive always_rooted:
[~empty:]
  (∀ψ. ψ.forest = FEMPTY ⇒ always_rooted ψ) ∧
[~step:]
  (∀ψ.
     all_rooted ψ ∧
     (∀p i.
        iforest_can_act ψ p ∧
        iforest_get ψ p = SOME i
        ⇒ always_rooted (iforest_step ψ p i))
     ⇒ always_rooted ψ)
End

Theorem fair_trace_cons:
  ∀procs p trace.
    fair_trace procs (p:::trace) ⇒ fair_trace procs trace
Proof
  rw[fair_trace_def]
QED

Theorem next_proc_fair_trace:
  ∀ψ procs trace p ll.
    fair_trace procs trace ∧
    next_proc ψ trace = SOME (p,ll)
    ⇒ fair_trace procs ll
Proof
  rw[] \\ drule next_proc_SOME
  \\ rw[] \\ Cases_on ‘trace’ \\ gs[]
  \\ irule fair_trace_cons
  \\ metis_tac []
QED

Theorem fair_trace_procs_subset:
  ∀procs trace procs'.
    fair_trace procs trace ∧
    procs' ⊆ procs
    ⇒ fair_trace procs' trace
Proof
  rw[fair_trace_def] \\ first_x_assum irule
  \\ gs[SUBSET_DEF]
QED

Theorem iforest_can_act_imp_next_proc:
∀ψ p trace.
  iforest_can_act ψ p ∧
  fair_trace {p} trace
  ⇒ ∃p ll. next_proc ψ trace = SOME (p,ll)
Proof
  rw[]
  \\ Cases_on ‘trace’
  \\ gs[next_proc_def,fair_trace_def]
  \\ drule iforest_can_act_in_itrees \\ rw[]
  \\ TOP_CASE_TAC \\ gs[LFILTER_EQ_NIL,every_LNTH]
  \\ Cases_on ‘n’ \\ gs[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem next_proc_imp_iforest_can_act:
  ∀ψ trace p ll.
    next_proc ψ trace = SOME (p,ll)
    ⇒ iforest_can_act ψ p
Proof
  rw[]
  \\ drule next_proc_SOME \\ rw[]
  \\ drule LFILTER_EQ_CONS \\ rw[]
QED

Theorem all_rooted_next_proc:
  ∀ψ procs trace.
    all_rooted ψ ∧
    fair_trace procs trace ∧
    iforest_itrees ψ ⊆ procs ∧
    ψ.forest ≠ FEMPTY
    ⇒ ∃p ll. next_proc ψ trace = SOME (p,ll)
Proof
  rw[all_rooted_def]
  \\ dxrule_all fair_trace_procs_subset
  \\ strip_tac
  \\ ‘∃p. p ∈ iforest_itrees ψ’ by
    (gs[iforest_itrees_def]
     \\ CCONTR_TAC \\ gs[FDOM_F_FEMPTY1])
  \\ gs[] \\ first_x_assum drule
  \\ pop_assum kall_tac
  \\ last_x_assum kall_tac
  \\ strip_tac
  \\ last_x_assum mp_tac
  \\ qid_spec_tac ‘trace’
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘p’,‘ψ’]
  \\ ho_match_mp_tac rooted_ind \\ rw[]
  >- (irule iforest_can_act_imp_next_proc
      \\ irule_at Any fair_trace_procs_subset
      \\ asm_exists_tac \\ simp[]
      \\ first_assum (irule_at Any)
      \\ irule iforest_can_act_in_itrees
      \\ simp[])
  >- (irule iforest_can_act_imp_next_proc
      \\ irule_at Any fair_trace_procs_subset
      \\ asm_exists_tac \\ simp[]
      \\ first_assum (irule_at Any)
      \\ irule iforest_can_act_in_itrees
      \\ simp[])
QED

Theorem always_rooted_weak_deadlock_freedom:
  ∀ψ trace procs.
    fair_trace procs trace ∧
    iforest_itrees ψ ⊆ procs ∧
    always_rooted ψ
    ⇒ weak_deadlock_freedom (iforest_itrees ψ) (iforest ψ trace)
Proof
  rw[]
  \\ irule (MP_CANON weak_deadlock_freedom_iforest_coind)
  \\ qexists_tac ‘λψ trace. fair_trace procs trace ∧
                            iforest_itrees ψ ⊆ procs ∧
                            always_rooted ψ’
  \\ rw[] \\ ntac 3 (last_x_assum kall_tac)
  \\ qmatch_goalsub_rename_tac ‘next_proc ψ trace’
  \\ gs[Once always_rooted_cases]
  \\ Cases_on ‘ψ.forest = FEMPTY’ \\ gs[]
  \\ first_x_assum (irule_at Any)
  \\ drule_all all_rooted_next_proc
  \\ rw[] \\ first_assum (irule_at Any)
  \\ drule next_proc_ifores_get_SOME \\ rw[]
  \\ first_assum (irule_at Any)
  \\ conj_tac
  \\ metis_tac [next_proc_imp_iforest_can_act
               ,next_proc_fair_trace
               ,iforest_itrees_mono_step
               ,iforest_can_act_in_itrees
               ,SUBSET_TRANS
               ]
QED

Theorem always_rooted_weak_deadlock_freedom':
  ∀ψ trace procs.
    fair_trace (iforest_itrees ψ) trace ∧
    always_rooted ψ
    ⇒ weak_deadlock_freedom (iforest_itrees ψ) (iforest ψ trace)
Proof
  rw[] \\ irule always_rooted_weak_deadlock_freedom \\ simp[]
  \\ first_x_assum (irule_at Any)
  \\ simp[]
QED

val _ = export_theory();
