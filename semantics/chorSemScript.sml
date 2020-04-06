open preamble choreoUtilsTheory

open chorLangTheory

val _ = new_theory "chorSem";

Datatype:
  label = LTau proc varN
        | LCom proc varN proc varN
        | LSel proc bool proc
        | LLet varN proc (datum list -> datum) (varN list)
End

Definition freeprocs_def:
  freeprocs (LTau p n)         = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LLet v p f vl)     = {p}
End

Definition sender_def:
  sender (LTau p n)          = NONE
∧ sender (LCom p1 v1 p2 v2)  = SOME p1
∧ sender (LSel p1 b p2)      = SOME p1
∧ sender (LLet v p f vl)     = NONE
End

Definition receiver_def:
  receiver (LTau p n)          = NONE
∧ receiver (LCom p1 v1 p2 v2)  = SOME p2
∧ receiver (LSel p1 b p2)      = SOME p2
∧ receiver (LLet v p f vl)     = NONE
End

Definition written_def:
  written (LTau p n)          = NONE
∧ written (LCom p1 v1 p2 v2)  = SOME(v2,p2)
∧ written (LSel p1 b p2)      = NONE
∧ written (LLet v p f vl)     = SOME(v,p)
End

Definition read_def:
  read (LTau p n)          = {(n,p)}
∧ read (LCom p1 v1 p2 v2) = {(v1,p1)}
∧ read (LSel p1 b p2)     = {}
∧ read (LLet v p f vl)     = set(MAP (λv. (v,p)) vl)
End

(* The set of all processes in a choreography *)
Definition procsOf_def:
  procsOf  Nil             = []
∧ procsOf (IfThen _ p l r) = nub' ([p] ++ procsOf l ++ procsOf r)
∧ procsOf (Com p _ q _ c)  = nub' ([p;q] ++ procsOf c)
∧ procsOf (Sel p _ q c)    = nub' ([p;q] ++ procsOf c)
∧ procsOf (Let _ p _ _ c)  = nub' ([p] ++ procsOf c)
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

val _ = Parse.add_infix("τ≅",425,Parse.NONASSOC);
val _ = Parse.overload_on("τ≅",``lcong``);

val [lcong_sym,lcong_refl,lcong_trans,lcong_reord] =
    zip ["lcong_sym","lcong_refl","lcong_trans","lcong_reord"]
        (CONJUNCTS lcong_rules) |> map save_thm;

Inductive trans:
  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME d
    ∧ p1 ≠ p2
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LCom p1 v1 p2 v2,[]) (s |+ ((v2,p2),d),c))

  (* Selection *)
∧ (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ trans (s,Sel p1 b p2 c) (LSel p1 b p2,[]) (s,c))

  (* Let *)
∧ (∀s v p f vl c.
    EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl))
    ⇒ trans (s,Let v p f vl c)
            (LLet v p f vl,[])
            (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl))),c))

  (* If (True) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c1))

  (* If (False) *)
∧ (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME w ∧ w ≠ [1w]
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c2))

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
    ∧ written alpha ≠ SOME (v1,p1)
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,LCom p1 v1 p2 v2::l) (s',Com p1 v1 p2 v2 c'))

∧ (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,LSel p1 b p2::l) (s',Sel p1 b p2 c'))
End


val _ = zip ["trans_com","trans_sel","trans_let","trans_if_true","trans_if_false",
              "trans_if_swap","trans_com_swap","trans_sel_swap","trans_let_swap",
              "trans_com_async","trans_sel_async"]
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
