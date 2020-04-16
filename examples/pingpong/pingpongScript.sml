open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
open chorLibProgTheory;
open fromSexpTheory;
open astToSexprLib;

open projectionLib;

val _ = new_theory "pingpong";

val _ = translation_extends "chorLibProg";

val n2w8 = “n2w:num -> word8”;

val ping = “MAP (^n2w8 o ORD) "ping"” |> EVAL |> concl |> rhs;
val pong = “MAP (^n2w8 o ORD) "pong"” |> EVAL |> concl |> rhs;

Definition KNil_def :
  KNil args = []
End

val _ = ml_prog_update (open_module "pingpong");

val _ = next_ml_names := ["KNil"];
Theorem KNil_v_thm = translate KNil_def;

val _ = ml_prog_update (close_module NONE);

Definition pingpong_def:
  pingpong =
  Let "v" ^ping (KNil) []
   (Com ^ping "v" ^pong "v"
     (Com ^pong "v" ^ping "v"
       Nil
     )
   )
End

val _ = project_to_camkes "pingpong_camkes" "pingpong" “pingpong”;

val (ping_to_cake_thm,ping_to_cake_wholeprog) = project_to_cake ``pingpong`` "ping" 1

val _ = astToSexprLib.write_ast_to_file "ping.sexp" ping_to_cake_wholeprog;

val _ = export_theory();
