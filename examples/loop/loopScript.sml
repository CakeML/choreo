open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
open chorLibProgTheory;
open fromSexpTheory;
open astToSexprLib;

open projectionLib;

val _ = new_theory "loop";

val _ = translation_extends "chorLibProg";

val n2w8 = “n2w:num -> word8”;

Definition KNil_def :
  KNil args = []
End

val _ = ml_prog_update (open_module "loop");

val _ = next_ml_names := ["KNil"];
Theorem KNil_v_thm = translate KNil_def;
Theorem K0_v_thm = translate endpoint_to_choiceTheory.K0_def;
val _ = ml_prog_update (close_module NONE);

Definition loop_def:
  loop =
  Let "v" "ping" (KNil) []
   (chorLang$Fix "X"
    (Com "ping" "v" "pong" "v"
      (Com "pong" "v" "ping" "v"
        (Call "X")
      )
    )
   )
End

val _ = project_to_camkes "loop_camkes" "loop" “loop”;

val _ = export_theory();
