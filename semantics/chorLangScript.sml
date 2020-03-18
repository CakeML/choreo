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
       | Letrec dvarN chor chor

       (* Process call*)
       | Call dvarN
`;

val _ = export_theory ()
