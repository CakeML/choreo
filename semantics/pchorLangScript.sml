open preamble;

val _ = new_theory "pchorLang";

val _ = type_abbrev( "varN" , ``: string``);

val _ = type_abbrev( "proc" , ``: string``); (* TODO: list -> mlvector? *)

val _ = type_abbrev( "datum" , ``: word8 list``); (* TODO: list -> mlvector? *)

(* Datatype for terms *)
val _ = Datatype`
  term = Var varN proc (* x@p variable x at process p *)
       | Datum datum   (* Some data *)
`;

val _ = Datatype`
  pchor = (* Termination *)
              Nil
              (* Eg:
                     0
               *)

            (* Branching *)
            |  IfThen varN proc pchor pchor
            (* IfThen e    p    C₁   C₂
               Eg:
                   if e@p then C₁ else C₂
             *)

            (* Communication *)
            |  Com proc varN proc varN pchor
            (* Com p    e    q    x    C
               Eg:
                  p.e → q.x ; C
             *)

            (* Partial communication (Receive is pending) *)
            |  PCom proc varN (proc # datum) pchor
            (* PCom q    x    (p   ,  v)     C
               Eg:
                  p.e → q.x ; C
                        ↑
                        Hasn't receive from p yet
             *)

            (* Scope *)
            |  Let varN proc (datum list -> datum) (varN list) pchor
            (* Let e    p    f                     args        C
               Eg:
                   let e@p = f args in C
             *)

            (* Selection *)
            |  Sel proc bool proc pchor
            (* Sel p    t    q    C
               Eg:
                   p[t] → q ; C
             *)

            (* Partial selection (Receive is pending) *)
            |  PSel proc (proc # bool) pchor
            (* PSel q    (p    , v)    C
               Eg:
                  p[t] → q ; C
                        ↑
                        Hasn't receive from p yet
             *)

`;

val _ = export_theory ()
