open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
open chorLibProgTheory;
open fromSexpTheory;
open astToSexprLib;

open projectionLib;

val _ = new_theory "hello";

val _ = translation_extends "chorLibProg";

val n2w8 = “n2w:num -> word8”;

val hello_world = “MAP (^n2w8 o ORD) "Hello World!"” |> EVAL |> concl |> rhs;

Definition KHello_def :
  KHello args = ^hello_world
End

val _ = ml_prog_update (open_module "hello");

val _ = next_ml_names := ["KHello"];
Theorem K0_v_thm = translate endpoint_to_choiceTheory.K0_def;
Theorem KHello_v_thm = translate KHello_def;

val _ = ml_prog_update (close_module NONE);

Definition hello_def:
  hello =
  Let "v" "ping" (KHello) []
   (Com "ping" "v" "pong" "v"
     (Com "pong" "v" "ping" "v"
       chorLang$Nil
     )
   )
End

val _ = project_to_camkes "hello_camkes" "hello" “hello”;

val _ = export_theory();
