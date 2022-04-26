open preamble;

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


val _ = export_theory ()
