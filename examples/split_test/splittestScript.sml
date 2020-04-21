open preamble chorLangTheory chorSemTheory projectionTheory
     payload_to_cakemlTheory basisProgTheory ml_translatorLib ml_progLib basisFunctionsLib;
open chorLibProgTheory;
open fromSexpTheory;
open astToSexprLib;

open projectionLib;

val _ = new_theory "splittest";

val _ = translation_extends "chorLibProg";

val n2w8 = “n2w:num -> word8”;

val ping = “MAP (^n2w8 o ORD) "ping"” |> EVAL |> concl |> rhs;
val pong = “MAP (^n2w8 o ORD) "pong"” |> EVAL |> concl |> rhs;

val splittest_world = “MAP (^n2w8 o ORD) "This message, on account of its gratuitous length, not only suggests that the author of this example writes preposterously redundant sentences and suffers from a severe inability to get to the point, but ought to be split up into multiple messages automatically by the send loop. Seeing that happen here would suggest that things are working as intended."” |> EVAL |> concl |> rhs;

Definition KSplittest_def :
  KSplittest args = ^splittest_world
End

val _ = ml_prog_update (open_module "splittest");

val _ = next_ml_names := ["KSplittest"];
Theorem KSplittest_v_thm = translate KSplittest_def;

val _ = ml_prog_update (close_module NONE);

Definition splittest_def:
  splittest =
  Let "v" ^ping (KSplittest) []
   (Com ^ping "v" ^pong "v"
     (Com ^pong "v" ^ping "v"
       Nil
     )
   )
End

val _ = project_to_camkes "splittest_camkes" "splittest" “splittest”;

val _ = export_theory();
