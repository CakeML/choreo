open HolKernel Parse boolLib bossLib preamble;
open llistTheory optionTheory itreesTheory finite_mapTheory;

val _ = new_theory "iforest";

(* iforest abstract definition *)

Datatype:
  itree_action = Ext 'a | Int | Res 'r
End

(* An Itree with a action ('a), event ('e), and result ('r) types *)
val itree  = “itree  : ('a,'e,'r) itree”
val itree' = “itree' : ('a,'e,'r) itree”

(* A forest is a finite mapping from some kind of identifier to an Itree *)
val _       = type_abbrev("forest",“:'p |-> ('a,'e,'r) itree”)
val forest  = “forest   : ('r,'e,'a,'p) forest”
val forest' = “forest'  : ('r,'e,'a,'p) forest”

(* Given an Itree identifier and an event which action should we perform? *)
val _    = type_abbrev("act",“:'p -> 'e -> 'a option”)
val act  = “act  : ('a,'e,'p) act”
val act' = “act' : ('a,'e,'p) act”

(* Given an (act)ed on Itree and event, how shoudl we update act? *)
val _    = type_abbrev("upd",“:'p -> 'e -> ('a,'e,'p) act -> ('a,'e,'p) act”)
val upd  = “upd  : ('a,'e,'p) upd”
val upd' = “upd' : ('a,'e,'p) upd”

Datatype:
  iforest = <| forest : 'p |-> ('a,'e,'r) itree ;
               act    : 'p -> 'e -> 'a option;
               upd    : 'p -> 'e ->
                        ('p -> 'e -> 'a option) ->
                         'p -> 'e -> 'a option
|>
End

val iforest = “ψ  :('a,'e,'p,'r) iforest”
val psi     = “ψ  :('a,'e,'p,'r) iforest”
val psi'    = “ψ' :('a,'e,'p,'r) iforest”


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
  iforest_upd_act ^iforest p e = ψ with act := ψ.upd p e ψ.act
End

Definition iforest_upd_def:
  iforest_upd ^iforest p e f =
    case ψ.act p e of
      NONE   => ψ
    | SOME a => ψ with <| forest := ψ.forest |+ (p,f a); act := ψ.upd p e ψ.act |>
End

Theorem iforest_upd_alt_def:
∀ψ p e f.
  IS_SOME (ψ.act p e) ⇒
  iforest_upd ψ p e f = iforest_upd_act (iforest_set ψ p (f (THE (ψ.act p e)))) p e
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
  | SOME (Vis e f) => IS_SOME (ψ.act p e)
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
  next_proc ^iforest trace =
    case LFILTER (λp. p ∈ iforest_itrees ψ ∧ iforest_can_act ψ p) trace of
      [||] => NONE
    | p:::ll => SOME (p,ll)
End

(* Properties of the basic iforest operations *)

Theorem next_proc_ifores_get_SOME:
  ∀ψ trace p ll.
    next_proc ψ trace = SOME (p,ll)
    ⇒ ∃i. iforest_get ψ p = SOME i
Proof
  rw[next_proc_def]
  \\ gs[CaseEq"llist"]
  \\ drule LFILTER_EQ_CONS
  \\ rw[iforest_can_act_def]
  \\ Cases_on ‘iforest_get ψ p’
  \\ gs[]
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
  \\ Cases_on ‘ψ.act p a’ \\ gs[]
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
      \\ gs[next_proc_def,CaseEq"llist"]
      \\ drule LFILTER_EQ_CONS
      \\ rw[] \\ CCONTR_TAC \\ gs[])
  >- (Cases_on ‘h’ \\ rw[] \\ gs[Once iforest_def]
      \\ Cases_on ‘next_proc ψ' trace’ \\ gs[]
      \\ Cases_on ‘x’ \\ gs[] \\ rveq
      \\ disj1_tac \\ qexists_tac ‘iforest_step ψ' q' (THE (iforest_get ψ' q'))’
      \\ qexists_tac ‘r'’ \\ simp[]
      \\ irule SUBSET_TRANS \\ first_x_assum (irule_at Any) \\ simp[]
      \\ irule iforest_itrees_mono_step
      \\ gs[next_proc_def,CaseEq"llist"]
      \\ drule LFILTER_EQ_CONS
      \\ rw[])
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

(* If an itree returns in the forest it never does any more actions *)
Theorem iforest_itree_end_aux[local]:
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

Theorem iforest_itrees_end:
  ∀n m ψ trace p t a.
    LNTH n (iforest ψ trace) = SOME (p, Res t) ∧ n < m ⇒
    LNTH m (iforest ψ trace) ≠ SOME (p,a)
Proof
  rw[]
  \\ drule iforest_itree_end_aux \\ rw[]
  \\ drule LESS_STRONG_ADD \\ rw[]
  \\ metis_tac []
QED


val _ = export_theory();
