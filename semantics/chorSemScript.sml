open preamble choreoUtilsTheory richerLangTheory envSemTheory

open chorLangTheory

val _ = new_theory "chorSem";

Datatype:
  label = LTau proc varN
        | LFix
        | LCom proc varN proc varN
        | LSel proc bool proc
        | LLet varN proc exp (exp value result)
        | LComExn proc varN proc varN
End

Definition freeprocs_def:
  freeprocs LFix               = {}
∧ freeprocs (LTau p n)         = {p}
∧ freeprocs (LCom p1 v1 p2 v2) = {p1;p2}
∧ freeprocs (LSel p1 b p2)     = {p1;p2}
∧ freeprocs (LLet v p e r)     = {p}
∧ freeprocs (LComExn p1 v1 p2 v2) = {p1;p2}
End

Definition sender_def:
  sender LFix                = NONE
∧ sender (LTau p n)          = NONE
∧ sender (LCom p1 v1 p2 v2)  = SOME p1
∧ sender (LSel p1 b p2)      = SOME p1
∧ sender (LLet v p e r)      = NONE
∧ sender (LComExn p1 v1 p2 v2)  = SOME p1
End

Definition receiver_def:
  receiver LFix                = NONE
∧ receiver (LTau p n)          = NONE
∧ receiver (LCom p1 v1 p2 v2)  = SOME p2
∧ receiver (LSel p1 b p2)      = SOME p2
∧ receiver (LLet v p e r)      = NONE
∧ receiver (LComExn p1 v1 p2 v2)  = SOME p2
End

Definition written_def:
  written LFix                = NONE
∧ written (LTau p n)          = NONE
∧ written (LCom p1 v1 p2 v2)  = SOME(v2,p2)
∧ written (LSel p1 b p2)      = NONE
∧ written (LLet v p e r)      = SOME(v,p)
∧ written (LComExn p1 v1 p2 v2)  = NONE
End

Definition read_def:
  read LFix               = {}
∧ read (LTau p n)         = {(n,p)}
∧ read (LCom p1 v1 p2 v2) = {(v1,p1)}
∧ read (LSel p1 b p2)     = {}
∧ read (LLet v p e r)     = {(s, p) | s ∈ free_vars e}
∧ read (LComExn p1 v1 p2 v2) = {(v1,p1)}
End

(* The set of all processes in a choreography *)
Definition procsOf_def:
  procsOf  Nil             = []
∧ procsOf (IfThen _ p l r) = nub' ([p] ++ procsOf l ++ procsOf r)
∧ procsOf (Com p _ q _ c)  = nub' ([p;q] ++ procsOf c)
∧ procsOf (Sel p _ q c)    = nub' ([p;q] ++ procsOf c)
∧ procsOf (Let _ p _ c)    = nub' ([p] ++ procsOf c)
∧ procsOf (Fix _ c)        = nub' (procsOf c)
∧ procsOf (Call _)         = []
End

(* The set of all free process variables in a choreography *)
Definition dvarsOf_def:
  dvarsOf  Nil             = []
∧ dvarsOf (IfThen _ p l r) = nub' (dvarsOf l ++ dvarsOf r)
∧ dvarsOf (Com p _ q _ c)  = nub' (dvarsOf c)
∧ dvarsOf (Sel p _ q c)    = nub' (dvarsOf c)
∧ dvarsOf (Let _ p _ c)    = nub' (dvarsOf c)
∧ dvarsOf (Fix dn c) = FILTER ($<> dn) (nub' (dvarsOf c))
∧ dvarsOf (Call dn)         = [dn]
End

Definition dprocsOf_def:
  dprocsOf dvars  Nil             = []
∧ dprocsOf dvars (IfThen _ p l r) = nub' ([p] ++ dprocsOf dvars l ++ dprocsOf dvars r)
∧ dprocsOf dvars (Com p _ q _ c)  = nub' ([p;q] ++ dprocsOf dvars c)
∧ dprocsOf dvars (Sel p _ q c)    = nub' ([p;q] ++ dprocsOf dvars c)
∧ dprocsOf dvars (Let _ p _ c)    = nub' ([p] ++ dprocsOf dvars c)
∧ dprocsOf dvars (Fix dn c) =
   nub' (dprocsOf ((dn,[])::dvars) c)
∧ dprocsOf dvars (Call dn)         =
   case ALOOKUP dvars dn of
     NONE => []
   | SOME procs => procs
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
∧ receiversOf pn (Let _ p _ c)       = nub' (receiversOf pn c)
∧ receiversOf pn (Fix _ c)    = nub'(receiversOf pn c)
∧ receiversOf pn (Call _) = []
End

(* let exps of *)
Definition letfunsOf_def:
  letfunsOf pn  Nil               = []
∧ letfunsOf pn (IfThen _ p l r)   = letfunsOf pn l ++ letfunsOf pn r
∧ letfunsOf pn (Com p _ q _ c)    = letfunsOf pn c
∧ letfunsOf pn (Sel p _ q c)      = letfunsOf pn c
∧ letfunsOf pn (Let _ p e c)      = (if p = pn then e::letfunsOf pn c else  letfunsOf pn c)
∧ letfunsOf pn (Fix _ c)    = letfunsOf pn c
∧ letfunsOf pn (Call _) = []
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
[~com:]
  (* Communication *)
  (∀s v1 p1 v2 p2 d c.
    FLOOKUP s (v1,p1) = SOME (StrV d)
    ∧ p1 ≠ p2
    ⇒ trans (s,Com p1 v1 p2 v2 c) (LCom p1 v1 p2 v2,[]) (s |+ ((v2,p2), (StrV d)),c))

(* com exn *)
[~com_exn:]
  ∀s v1 p1 v2 p2 c v.
  FLOOKUP s (v1,p1) = SOME v ∧ (∀s. v ≠ StrV s)
  ⇒ trans (s,Com p1 v1 p2 v2 c) (LComExn p1 v1 p2 v2,[]) (s,Nil)

[~sel:]
  (* Selection *)
  (∀s p1 b p2 c.
    p1 ≠ p2
    ⇒ trans (s,Sel p1 b p2 c) (LSel p1 b p2,[]) (s,c))

[~letval:]
  (∀s v p e c cl.
    eval_exp cl (localise s p) e = Value ev ∧ free_vars e ⊆ FDOM (localise s p) (* not sure *)
    ⇒ trans (s,Let v p e c)
            (LLet v p e (Value ev),[])
            (s |+ ((v,p), ev),c))

[~letexn:]
  (∀s v p e c cl exn.
    eval_exp cl (localise s p) e = Exn exn ∧ free_vars e ⊆ FDOM (localise s p)
    ⇒ trans (s,Let v p e c)
            (LLet v p e (Exn exn),[])
            (s, Nil))

[~if_true:]
  (* If (True) *)
  (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME (BoolV T)
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c1))

[~if_false:]
  (* If (False) *)
  (∀s v p c1 c2.
    FLOOKUP s (v,p) = SOME (BoolV F)
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s,c2))

[~if_exn:]
  (∀s v p c1 c2 w.
    FLOOKUP s (v,p) = SOME w ∧ ¬is_BoolV w
    ⇒ trans (s,IfThen v p c1 c2) (LTau p v,[]) (s, Nil))

(* Swapping transitions / Structural congruence *)

[~if_swap:]
  (∀s v p c1 c2 s' c1' c2' l l' alpha.
    trans (s,c1) (alpha,l) (s',c1')
    ∧ trans (s,c2) (alpha,l') (s',c2')
    ∧ l τ≅ l'
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,IfThen v p c1 c2) (alpha,l) (s',IfThen v p c1' c2'))

[~com_swap:]
  (∀s c s' c' p1 v1 p2 v2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,l) (s',Com p1 v1 p2 v2 c'))
[~sel_swap:]
  (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∉ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,l) (s',Sel p1 b p2 c'))
[~let_swap:]
  (∀s c s' c' p v e l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p ∉ freeprocs alpha
    ⇒ trans (s,Let v p e c) (alpha,l) (s',Let v p e c'))

  (* Asynchrony *)
[~com_async:]
  (∀s c s' c' p1 v1 p2 v2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ written alpha ≠ SOME (v1,p1)
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Com p1 v1 p2 v2 c) (alpha,LCom p1 v1 p2 v2::l)
            (s',Com p1 v1 p2 v2 c'))

[~sel_async:]
  (∀s c s' c' p1 b p2 l alpha.
    trans (s,c) (alpha,l) (s',c')
    ∧ p1 ∈ freeprocs alpha
    ∧ p2 ∉ freeprocs alpha
    ⇒ trans (s,Sel p1 b p2 c) (alpha,LSel p1 b p2::l) (s',Sel p1 b p2 c'))

   (* Recursion *)

[~fix:]
  (∀s c dn.
    trans (s,Fix dn c) (LFix,[]) (s,dsubst c dn (Fix dn c)))


[~fix_if_true:]
  (∀s v p c c0 c'.
    trans (s,c) (LFix,[]) (s,c')
    ⇒ trans (s,IfThen v p c c0) (LFix,[]) (s,IfThen v p c' c0))


[~fix_if_false:]
  (∀s v p c c0 c'.
    trans (s,c) (LFix,[]) (s,c')
    ⇒ trans (s,IfThen v p c0 c) (LFix,[]) (s,IfThen v p c0 c'))
End

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

(* A bunch of unfold operations *)
Definition trans_unfold_def:
  trans_unfold = RTC (λp q. trans p (LFix,[]) q)
End

val _ = export_theory ()
