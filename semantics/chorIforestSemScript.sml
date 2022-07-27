open preamble chorLangTheory
     itreesTheory iforestTheory itreeCommonTheory
     chorItreeSemTheory

val _ = new_theory "chorIforestSem";

Definition chor_iforest_act_def[simp]:
  chor_iforest_act s p (Send q d)   = SOME Ok
∧ chor_iforest_act s p (Choose q b) = SOME Ok
∧ chor_iforest_act s p (Receive q)  =
    (case FLOOKUP s (p,q) of
       NONE         => NONE
     | SOME []      => NONE
     | SOME (x::xs) => SOME (Msg x))
∧ chor_iforest_act s p (Select q)   =
      (case FLOOKUP s (p,q) of
       NONE         => NONE
     | SOME []      => NONE
     | SOME (x::xs) => SOME (Branch (x = [1w])))
End

Definition chor_iforest_upd_def[simp]:
  chor_iforest_upd s p (Send q d)   = s |+ ((p,q), the [] (FLOOKUP s (p,q)) ++ [d])
∧ chor_iforest_upd s p (Choose q b) = s |+ ((p,q), the [] (FLOOKUP s (p,q)) ++ [if b then [1w] else [0w]])
∧ chor_iforest_upd s p (Receive q)  = s |+ ((p,q), TL (the [] (FLOOKUP s (p,q))))
∧ chor_iforest_upd s p (Select q)   = s |+ ((p,q), TL (the [] (FLOOKUP s (p,q))))
End

Definition procs_s_def:
  procs_s p s = MAP_KEYS (λx. FST x) (DRESTRICT s (λx. SND x = p))
End

Definition chor_iforest_forest_def:
  chor_forest s c []         = FEMPTY
∧ chor_forest s c (p::procs) = (chor_forest s c procs) |+ (p,chor_itree p (procs_s p s) c)
End

val _ = Parse.overload_on("chor_ψ",``chor_forest``);

Definition chor_iforest_def:
  chor_iforest qs forest = <| forest := forest;
                              st     := qs;
                              upd    := chor_iforest_upd;
                              act    := chor_iforest_act;
                           |>
End

Definition plant_chor_iforest_def:
  plant_chor_iforest c = chor_iforest FEMPTY (chor_ψ FEMPTY c (procsOf c))
End

val _ = export_theory ()
