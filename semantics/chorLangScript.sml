open preamble choreoUtilsTheory;

val _ = new_theory "chorLang";

val _ = type_abbrev( "varN" , ``: string``);

val _ = type_abbrev( "dvarN" , ``: string``); (* Process definition variable *)

val _ = type_abbrev( "proc" , ``: string``); (* TODO: list -> mlvector? *)

val _ = type_abbrev( "datum" , ``: word8 list``); (* TODO: list -> mlvector? *)

(* Datatype for terms *)
val _ = Datatype`
  term = Var varN proc (* x@p variable x at process p *)
       | Datum datum   (* Some data *)
(* TODO: Add more datatypes? *)
`;

val _ = Datatype`
  chor = (* Termination *)
         Nil
         (* Eg:
                0
          *)

       (* Branching *)
       |  IfThen varN proc chor chor
       (* IfThen e    p    C₁   C₂
          Eg:
              if e@p then C₁ else C₂
        *)

       (* Communication *)
       |  Com proc varN proc varN chor
       (* Com p    e    q    x    C
          Eg:
             p.e → q.x ; C
        *)

       (* Scope *)
       |  Let varN proc (datum list -> datum) (varN list) chor
       (* Let e    p    f                     args        C
          Eg:
              let e@p = f args in C
        *)
       (* TODO: is this ok? *)

       (* Selection *)
       |  Sel proc bool proc chor
       (* Sel p    t    q    C
          Eg:
              p[t] → q ; C
        *)

       (* Process definition *)
       | Fix dvarN chor

       (* Process call*)
       | Call dvarN
`;

(* Substitution *)
Definition dsubst_def:
  dsubst Nil dn c'               = Nil
∧ dsubst (IfThen v p l r) dn c' = IfThen v p (dsubst l dn c') (dsubst r dn c')
∧ dsubst (Com p v1 q v2 c) dn c'  = Com p v1 q v2 (dsubst c dn c')
∧ dsubst (Sel p v q c) dn c'    = Sel p v q (dsubst c dn c')
∧ dsubst (Let v p f l c) dn c'  = Let v p f l (dsubst c dn c')
∧ dsubst (Fix dn' c) dn c' =
   (if dn = dn' then
      Fix dn' c
    else
      Fix dn' (dsubst c dn c'))
∧ dsubst (Call dn') dn c'          =
   (if dn = dn' then
      c'
    else
      Call dn')
End

Definition size_chor_def:
  size_chor Nil                = (1 : num)
∧ size_chor (Com _ _ _ _ c)    = 1 + size_chor c
∧ size_chor (Sel _ _ _ c)      = 1 + size_chor c
∧ size_chor (Let _ _ _ _ c)    = 1 + size_chor c
∧ size_chor (IfThen _ _ c1 c2) = 1 + size_chor c1 + size_chor c2
∧ size_chor (Fix dn c)         = 1 + size_chor c
∧ size_chor (Call dn)          = 1
End

(* The set of all processes in a choreography *)
Definition procsOf_def:
  procsOf  Nil             = []
∧ procsOf (IfThen _ p l r) = nub' ([p] ++ procsOf l ++ procsOf r)
∧ procsOf (Com p _ q _ c)  = nub' ([p;q] ++ procsOf c)
∧ procsOf (Sel p _ q c)    = nub' ([p;q] ++ procsOf c)
∧ procsOf (Let _ p _ _ c)  = nub' ([p] ++ procsOf c)
∧ procsOf (Fix _ c) = nub' (procsOf c)
∧ procsOf (Call _)         = []
End

(* The error choreography:

   (1) Projectable choreography should not contain it.
   (2) It always produces an error result
 *)
Definition CERROR:
  CERROR = Call "ERROR"
End

(* The set of all free process variables in a choreography *)
Definition dvarsOf_def:
  dvarsOf  Nil             = []
∧ dvarsOf (IfThen _ p l r) = nub' (dvarsOf l ++ dvarsOf r)
∧ dvarsOf (Com p _ q _ c)  = nub' (dvarsOf c)
∧ dvarsOf (Sel p _ q c)    = nub' (dvarsOf c)
∧ dvarsOf (Let _ p _ _ c)  = nub' (dvarsOf c)
∧ dvarsOf (Fix dn c) = FILTER ($<> dn) (nub' (dvarsOf c))
∧ dvarsOf (Call dn)         = [dn]
End

Definition dprocsOf_def:
  dprocsOf dvars  Nil             = []
∧ dprocsOf dvars (IfThen _ p l r) = nub' ([p] ++ dprocsOf dvars l ++ dprocsOf dvars r)
∧ dprocsOf dvars (Com p _ q _ c)  = nub' ([p;q] ++ dprocsOf dvars c)
∧ dprocsOf dvars (Sel p _ q c)    = nub' ([p;q] ++ dprocsOf dvars c)
∧ dprocsOf dvars (Let _ p _ _ c)  = nub' ([p] ++ dprocsOf dvars c)
∧ dprocsOf dvars (Fix dn c) =
   nub' (dprocsOf ((dn,[])::dvars) c)
∧ dprocsOf dvars (Call dn)         =
   case ALOOKUP dvars dn of
     NONE => []
   | SOME procs => nub' procs
End

Theorem procsOf_all_distinct:
  ∀c. ALL_DISTINCT (procsOf c)
Proof
  Induct_on `c` >> rw [procsOf_def,ALL_DISTINCT,all_distinct_nub']
QED

val _ = export_theory ()
