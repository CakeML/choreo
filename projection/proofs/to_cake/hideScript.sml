open HolKernel Parse boolLib bossLib;

open stringTheory
val _ = new_theory "hide";

Definition hide_def:
  hide (s:string) (x:bool) = x
End

Theorem hideCONG:
  hide s x = hide s x
Proof
  simp[]
QED

val _ = export_theory();
