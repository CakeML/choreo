open HolKernel Parse boolLib bossLib preamble;
open llistTheory optionTheory itreesTheory finite_mapTheory;

val _ = new_theory "iforest";

(* Type aliases *)

(* An Itree with a action ('a), event ('e), and result ('r) types *)
val itree  = “itree  : ('a,'e,'r) itree”

(* A forest is a finite mapping from some kind of identifier to an Itree *)
val forest = “forest : 'p |-> ('a,'e,'r) itree”

(* Given an Itree identifier and an event which action should we perform? *)
val act    = “act    : 'p -> 'e -> 'a option”

(* Given an (act)ed on Itree and event, how shoudl we update act? *)
val upd    = “upd    : 'p -> 'e ->
                       ('p -> 'e -> 'a option) ->
                       'p -> 'e -> 'a option”


(* A trace is a stream of Itree identifiers to operate over.
   It is meant to represent in which order the forest is being
   evaluated. For most useful proofs about a forest some notion
   of fair trace might be needed.
*)
val trace  = “trace  : 'p llist”

(* Folding function to be used with  LUNFOLD *)
Definition iforest_aux1_def:
  (* If the stream is empty we are done *)
  iforest_aux (^act,^upd,^forest,[||]) = NONE
  (* When an Itree p is selected *)
∧ iforest_aux (^act,^upd,^forest,p:::^trace) =
  (* Check if the Itree is in the forest *)
  case FLOOKUP forest p of
    (* If there is no such ITree, move on, this is (somewhat) weird *)
    NONE           => SOME ((act,upd,forest,trace),NONE)
  (* If the Itree has return, move on to another Itree (continue) *)
  | SOME (Ret t)   => SOME ((act,upd,forest,trace),NONE)
  (* If the Itree is in an internal transition advance and update the Iforest *)
  | SOME (Tau t)   => SOME ((act,upd,forest |+ (p, t),trace),NONE)
  (* If the Itree returns an event:  *)
  | SOME (Vis e f) =>
      (* See if we can act on it *)
      case act p e of
        (* If we (currently) can not act, then move on to anaother Itree.
           The hope here is that maybe after some other Itrees in the forest
           have been acted on we could come back and be able to do something.
         *)
        NONE   => SOME ((act,upd,forest,trace),NONE)
      (* If we can act, do so and update the act function according to upd.
         Once we act on an event we record it to the stream
       *)
      | SOME a => SOME ((upd p e act,upd,forest |+ (p, f a),trace),SOME e)
End

(* To create the stream of events we filter out all the NONE element from
   Ret and Tau Itrees
*)
Definition iforest_aux_def:
  iforest ^act ^upd ^forest ^trace =
    LMAP THE (LFILTER IS_SOME (LUNFOLD iforest_aux (act,upd,forest,trace)))
End

(* Much nicer version of iforest.
   - Comments are duplicated from iforest_aux1_def
 *)

Theorem iforest_def[compute]:
∀ ^act ^upd ^forest p ^trace.
  (* If the stream is empty we are done *)
  iforest act upd forest  [||] = [||]
  (* When an Itree p is selected *)
∧ iforest act upd forest (p:::^trace) =
  (* Check if the Itree is in the forest *)
  case FLOOKUP forest p of
    (* If there is no such ITree, move on, this is (somewhat) weird *)
    NONE           => iforest act upd forest             trace
  (* If the Itree has return, move on to another Itree (continue) *)
  | SOME (Ret t)   => iforest act upd forest             trace
  (* If the Itree is in an internal transition advance and update the Iforest *)
  | SOME (Tau t)   => iforest act upd (forest |+ (p, t)) trace
  (* If the Itree returns an event:  *)
  | SOME (Vis e f) =>
      (* See if we can act on it *)
      case act p e of
        (* If we (currently) can not act, then move on to anaother Itree.
           The hope here is that maybe after some other Itrees in the forest
           have been acted on we could come back and be able to do something.
         *)
        NONE   => iforest act upd forest trace
      (* If we can act, do so and update the act function according to upd.
         Once we act on an event we record it to the stream
       *)
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
