open preamble astBakeryTheory;

val _ = new_theory "semBakery";

val evaluate_def = Define `
  (evaluate s Nil = SOME s) ∧
  (evaluate s (Com p1 v1 p2 v2 c) =
   if p1 ≠ p2 then
     case FLOOKUP s (v1,p1) of
         SOME d => evaluate (s |+ ((v2,p2),d)) c
       | NONE => NONE
   else NONE) ∧
  (evaluate s (Sel p1 b p2 c) =
   if p1 ≠ p2 then
     evaluate s c
   else
     NONE) ∧
  (evaluate s (Let v p f vl c) =
   if EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) vl)) then
     evaluate (s |+ ((v,p),f(MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) vl)))) c
   else
     NONE) ∧
  (evaluate s (IfThen v p c1 c2) =
   case FLOOKUP s (v,p) of
       NONE => NONE
     | SOME wl =>
       if wl = [1w] then
         evaluate s c1
       else
         evaluate s c2)`
                                
val _ = export_theory ()
