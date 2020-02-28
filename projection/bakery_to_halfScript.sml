open preamble semBakeryTheory semHalfBakeryTheory

val _ = new_theory "bakery_to_half"

Definition project_def:
  project astBakery$Nil      = astHalfBakery$Nil
∧ project (Com p v q x c)    = Com p v q x (project c)
∧ project (Sel p b q c)      = Sel p b q (project c)
∧ project (Let e p f a c)    = Let e p f a (project c)
∧ project (IfThen v p c1 c2) = IfThen v p (project c1) (project c2)
End

val _ = export_theory ()
