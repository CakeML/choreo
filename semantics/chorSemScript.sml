open preamble choreoUtilsTheory

open chorLangTheory

val _ = new_theory "chorSem";

Datatype:
  label = LTau proc varN
        | LCom proc varN proc varN
        | LSel proc bool proc
        | LLet varN proc (datum list -> datum) (varN list)
        | LLetrec ((varN # proc) set)
        | LRec ((varN # proc) list)
End

Definition freeprocs_def:
  freeprocs (LTau p n)          = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LLet v p f vl)    = {p}
∧ freeprocs (LLetrec vl)    = IMAGE SND vl
∧ freeprocs (LRec vl)          = set(MAP SND vl)
End

Definition sender_def:
   sender (LTau p n)          = NONE
∧ sender (LCom p1 v1 p2 v2)  = SOME p1
∧ sender (LSel p1 b p2)      = SOME p1
∧ sender (LLet v p f vl)     = NONE
∧ sender (LRec vl)           = NONE
End

Definition receiver_def:
  receiver (LTau p n)           = NONE
∧ receiver (LCom p1 v1 p2 v2)  = SOME p2
∧ receiver (LSel p1 b p2)      = SOME p2
∧ receiver (LLet v p f vl)     = NONE
∧ receiver (LLetrec vl)        = NONE
∧ receiver (LRec vl)           = NONE
End

Definition written_def:
  written (LTau p n)          = {}
∧ written (LCom p1 v1 p2 v2) = {(v2,p2)}
∧ written (LSel p1 b p2)     = {}
∧ written (LLet v p f vl)    = {(v,p)}
∧ written (LLetrec vl)       = vl
∧ written (LRec vl)          = {}
End

Definition read_def:
  read (LTau p n)          = {(n,p)}
∧ read (LCom p1 v1 p2 v2) = {(v1,p1)}
∧ read (LSel p1 b p2)     = {}
∧ read (LLet v p f vl)    = set(MAP (λv. (v,p)) vl)
∧ read (LLetrec vl)       = vl
∧ read (LRec vl)          = set vl
End

(* The set of all processes in a choreography *)
Definition procsOf_def:
  procsOf  Nil             = []
∧ procsOf (IfThen _ p l r) = nub' ([p] ++ procsOf l ++ procsOf r)
∧ procsOf (Com p _ q _ c)  = nub' ([p;q] ++ procsOf c)
∧ procsOf (Sel p _ q c)    = nub' ([p;q] ++ procsOf c)
∧ procsOf (Let _ p _ _ c)  = nub' ([p] ++ procsOf c)
∧ procsOf (Letrec _ vl c c')  = nub' (procsOf c ++ procsOf c' ++ MAP SND vl)
∧ procsOf (Call _ vl)  = nub' (MAP SND vl)
End

Theorem procsOf_all_distinct:
  ∀c. ALL_DISTINCT (procsOf c)
Proof
  Induct_on `c` >> rw [procsOf_def,ALL_DISTINCT,all_distinct_nub']
QED


(* The set of all processes in a choreography that need to receive from a specific process *)
Definition receiversOf_def:
  receiversOf pn  Nil               = []
∧ receiversOf pn (IfThen _ p l r)   = nub' (receiversOf pn l ++ receiversOf pn r)
∧ (receiversOf pn (Com p _ q _ c)    = if p = pn then nub' (q::receiversOf pn c)
                                       else nub' (receiversOf pn c))
∧ (receiversOf pn (Sel p _ q c)      = if p = pn then nub' (q::receiversOf pn c)
                                       else nub' (receiversOf pn c))
∧ receiversOf pn (Let _ p _ _ c)    = nub' (receiversOf pn c)
∧ receiversOf pn (Letrec _ _ c c')  = nub' (receiversOf pn c ++ receiversOf pn c')
∧ receiversOf pn (Call _ _)         = []
End

Definition letfunsOf_def:
   letfunsOf pn  Nil               = []
∧ letfunsOf pn (IfThen _ p l r)   = letfunsOf pn l ++ letfunsOf pn r
∧ letfunsOf pn (Com p _ q _ c)    = letfunsOf pn c
∧ letfunsOf pn (Sel p _ q c)      = letfunsOf pn c
∧ letfunsOf pn (Let _ p f _ c)    = (if p = pn then f::letfunsOf pn c else  letfunsOf pn c)
∧ letfunsOf pn (Letrec _ _ c c')  = letfunsOf pn c ++ letfunsOf pn c'
∧ letfunsOf pn (Call _ _)           = []
End

Definition free_variables_def:
  (free_variables (Nil) = {}) /\
  (free_variables (IfThen v p c1 c2) = {(v,p)} ∪ (free_variables c1 ∪ free_variables c2)) ∧
  (free_variables (Com p1 v1 p2 v2 c) = {(v1,p1)} ∪ (free_variables c DELETE (v2,p2))) ∧
  (free_variables (Let v p f vl c) = set(MAP (λv. (v,p)) vl) ∪ (free_variables c DELETE (v,p))) ∧
  (free_variables (Sel p b q c) = free_variables c) ∧
  (free_variables (Letrec n vl c c') = ((free_variables c DIFF set vl) ∪ free_variables c')) ∧
  (free_variables (Call n vl) = set vl)
End

Inductive lcong:
(* Congruence rules for lists of asyncronous operations *)

  (* Symmetric *)
  (∀l. lcong l l)

  (* Reflexive *)
∧ (∀l1 l2.
    lcong l1 l2
    ⇒ lcong l2 l1)
  (* Transitive *)
∧ (∀l1 l2 l3.
     lcong l1 l2
     ∧ lcong l2 l3
     ⇒ lcong l1 l3)

  (* Reorder *)
∧ (∀h t t1 t2.
    DISJOINT (freeprocs t1) (freeprocs t2)
    ⇒ lcong (h ++ [t1;t2] ++ t) (h ++ [t2;t1] ++ t))
End

Datatype:
  chor_state =
  <| vars : (varN #proc) |-> datum;
     funs : (varN,'v) alist
   |>
End

Datatype:
 closure = Closure ((varN#proc) list) (closure chor_state) chor
End

val _ = Parse.add_infix("τ≅",425,Parse.NONASSOC);
val _ = Parse.overload_on("τ≅",``lcong``);

val [lcong_sym,lcong_refl,lcong_trans,lcong_reord] =
    zip ["lcong_sym","lcong_refl","lcong_trans","lcong_reord"]
        (CONJUNCTS lcong_rules) |> map save_thm;

Inductive trans:
  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s.vars (v1,p1) = SOME d
    ∧ p1 ≠ p2
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LCom p1 v1 p2 v2,[]) (s with vars := s.vars |+ ((v2,p2),d),c))

  (* Selection *)
∧ (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ trans (s,Sel p1 b p2 c) (LSel p1 b p2,[]) (s,c))

  (* Let *)
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s.vars) (MAP (λv. (v,p)) vl))
    ⇒ trans (s,Let v p f vl c)
            (LLet v p f vl,[])
            (s with vars := s.vars |+ ((v,p),f(MAP (THE o FLOOKUP s.vars) (MAP (λv. (v,p)) vl))),c))

  (* If (True) *)
∧ (∀s v p c1 c2.
    FLOOKUP s.vars (v,p) = SOME [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c1))

  (* If (False) *)
∧ (∀s v p c1 c2.
    FLOOKUP s.vars (v,p) = SOME w ∧ w ≠ [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c2))

   (* Letrec *)
∧ (∀s v params c1 c2.
    trans
      (s,Letrec v params c1 c2)
      (LLetrec (free_variables c1 DIFF set params),[])
      (s with funs := (v,
                       Closure params
                               (s with vars := DRESTRICT s.vars
                                                         (free_variables c1 DIFF set params))
                               c1)::s.funs,
       c2))

   (* Call *)
∧ (∀s v args params s' c.
    ALL_DISTINCT args ∧
    EVERY IS_SOME (MAP (FLOOKUP s.vars) args) ∧
    MAP FST params = MAP FST args ∧
    ALOOKUP s.funs v = SOME (Closure params s' c)
    ⇒ trans
        (s,Call v args)
        (LRec vl,[])
        (s' with <| vars := (s'.vars ⊌ s.vars) |++ ZIP (params,MAP (THE o FLOOKUP s.vars) args);
                    funs := (v,Closure params s' c)::s'.funs
                 |>,
         c))

  (* Swapping transitions / Structural congruence *)
∧ (∀s v p c1 c2 s' c1' c2' l l' alpha.
    trans (s,c1) (alpha,l) (s',c1')
    ∧ trans (s,c2) (alpha,l') (s',c2')
    ∧ l τ≅ l'
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,IfThen v p c1 c2) (alpha,l) (s',IfThen v p c1' c2'))
∧ (∀s c s' c' p1 v1 p2 v2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,l) (s',Com p1 v1 p2 v2 c'))
∧ (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,l) (s',Sel p1 b p2 c'))
∧ (∀s c s' c' p v f vl l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,Let v p f vl c) (alpha,l) (s',Let v p f vl c'))

  (* Asynchrony *)
∧ (∀s c s' c' p1 v1 p2 v2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ (v1,p1) ∉ written alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,LCom p1 v1 p2 v2::l) (s',Com p1 v1 p2 v2 c'))

∧ (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,LSel p1 b p2::l) (s',Sel p1 b p2 c'))
End

val _ = zip ["trans_com","trans_sel","trans_let","trans_if_true","trans_if_false",
             "trans_letrec","trans_call","trans_if_swap","trans_com_swap",
             "trans_sel_swap","trans_let_swap","trans_com_async","trans_sel_async"]
            (CONJUNCTS trans_rules) |> map save_thm;

Theorem trans_pairind =
  theorem"trans_strongind"
  |> Q.SPEC `λa0 a1 a2. P (FST a0) (SND a0) (FST a1) (SND a1)  (FST a2) (SND a2)`
  |> SIMP_RULE std_ss [FORALL_PROD]
  |> Q.GEN `P`

(* Reflexive transitive closure *)
Definition trans_s_def:
  trans_s = RTC (λp q. ∃s. trans p s q)
End

(* A synchronous version of ‘trans_s’ *)
Definition trans_sync_def:
  trans_sync = RTC (λp q. ∃τ. trans p (τ,[]) q)
End

val _ = export_theory ()
