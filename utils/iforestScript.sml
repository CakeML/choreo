open HolKernel Parse boolLib bossLib preamble;
open llistTheory optionTheory itreeTheory finite_mapTheory;

val _ = new_theory "iforest";

val itree  = “itree  : ('a,'e,'r) itree”
val act    = “act    : 'p -> 'e -> 'a option”
val upd    = “upd    : 'p -> 'e ->
                       ('p -> 'e -> 'a option) ->
                       'p -> 'e -> 'a option”

val forest = “forest : 'p |-> ('a,'e,'r) itree”
val trace  = “trace  : 'p llist”

Definition iforest_aux1_def:
  iforest_aux (^act,^upd,^forest,[||]) = NONE
∧ iforest_aux (^act,^upd,^forest,p:::^trace) =
  case FLOOKUP forest p of
    NONE           => SOME ((act,upd,forest,trace),NONE)
  | SOME (Ret t)   => SOME ((act,upd,forest,trace),NONE)
  | SOME (Tau t)   => SOME ((act,upd,forest |+ (p, t),trace),NONE)
  | SOME (Vis e f) =>
      case act p e of
        NONE   => SOME ((act,upd,forest,trace),NONE)
      | SOME a => SOME ((upd p e act,upd,forest |+ (p, f a),trace),SOME e)
End

Definition iforest_aux_def:
  iforest ^act ^upd ^forest ^trace =
    LMAP THE (LFILTER IS_SOME (LUNFOLD iforest_aux (act,upd,forest,trace)))
End

Theorem iforest_def[compute]:
∀ ^act ^upd ^forest p ^trace.
  iforest act upd forest  [||] = [||]
∧ iforest act upd forest (p:::^trace) =
  case FLOOKUP forest p of
    NONE           => iforest act upd forest             trace
  | SOME (Ret t)   => iforest act upd forest             trace
  | SOME (Tau t)   => iforest act upd (forest |+ (p, t)) trace
  | SOME (Vis e f) =>
      case act p e of
        NONE   => iforest act upd forest trace
      | SOME a => e ::: iforest (upd p e act) upd (forest |+ (p, f a)) trace
Proof
  rw[iforest_aux_def]
  >- simp[Once LUNFOLD,iforest_aux1_def]
  \\ Cases_on ‘FLOOKUP forest p’
  >- simp[Once LUNFOLD,iforest_aux1_def]
  \\ Cases_on ‘x’
  >~ [‘Vis a g’]
  >- (Cases_on ‘act p a’ \\ simp[Once LUNFOLD,iforest_aux1_def])
  \\ simp[Once LUNFOLD,iforest_aux1_def]
QED

val _ = export_theory();
