(*
  This file defines a type for potentially infinite interaction
  trees. We take inspiration from the itree type of Xia et al.'s
  POPL'20 paper titled "Interaction Trees".
  Interaction trees are interesting because they can both represent a
  program's observable I/O behaviour and also model of the I/O
  behaviour of the external world.
  Our version of the type for interaction trees, itree, has the
  following constructors.  Here Ret ends an interaction tree with a
  return value; Tau is the silent action; Vis is a visible event that
  returns a value that the rest of the interaction tree can depend on.
    ('a,'e,'r) itree  =
       Ret 'r                           --  termination with result 'r
    |  Tau (('a,'e,'r) itree)           --  a silent action, then continue
    |  Vis 'e ('a -> ('a,'e,'r) itree)  --  visible event 'e with answer 'a,
                                            then continue based on answer
*)

(* From: CakeML/pure@b59704236455aa6c76105cf7931273093c4c36a9 *)
(* Author: Magnus Myreen *)

open HolKernel Parse boolLib bossLib;

open itreeTauTheory;

(* open arithmeticTheory listTheory llistTheory alistTheory optionTheory; *)
(* open mp_then pred_setTheory relationTheory pairTheory combinTheory; *)

val _ = new_theory "itreeProps";

(* misc *)

Definition spin:
  spin = itree_unfold (K (Tau' ())) ()
End

Theorem spin:
  spin = Tau spin  (* an infinite sequence of silent actions *)
Proof
  fs [spin] \\ simp [Once itree_unfold]
QED

(* Better equality *)

CoInductive itree_eqv:
[~ret:]
  (x = y ⇒ itree_eqv (Ret x) (Ret y)) ∧
[~tau:]
  (itree_eqv l r ⇒ itree_eqv (Tau l) (Tau r)) ∧
[~vis:]
    ((∀a. itree_eqv (f a) (g a)) ∧ e1 = e2 ⇒ itree_eqv (Vis e1 f) (Vis e2 g))
End


Theorem itree_eqv_sym:
  ∀x1 x2. itree_eqv x2 x1 ⇒ itree_eqv x1 x2
Proof
  ho_match_mp_tac itree_eqv_coind \\ rw[]
  \\ gs[Once itree_eqv_cases]
  \\ metis_tac []
QED

Theorem itree_eqv_refl:
  ∀x. itree_eqv x x
Proof
  rw[]
  \\ ho_match_mp_tac (MP_CANON itree_eqv_coind) \\ rw[]
  \\ qexists_tac ‘$=’ \\ rw[]
  \\ Cases_on ‘a0’ \\ metis_tac[]
QED

Theorem itree_eqv_eq:
  ∀x y. itree_eqv x y ⇔ x = y
Proof
  rw[] \\ EQ_TAC \\ gs[itree_eqv_refl]
  \\ rw[Once itree_bisimulation]
  \\ qexists_tac ‘itree_eqv’
  \\ rw[]
  \\ pop_assum (mp_tac o ONCE_REWRITE_RULE [itree_eqv_cases])
  \\ rw[itree_distinct]
QED

Definition itree_eqn_def:
  itree_eqn 0 x y = T
∧ itree_eqn n (Ret x) (Ret y) = (x = y)
∧ itree_eqn (SUC n) (Tau l) (Tau r) = itree_eqn n l r
∧ itree_eqn (SUC n) (Vis e1 f) (Vis e2 g) = (e1 = e2 ∧ ∀a. itree_eqn n (f a) (g a))
∧ itree_eqn n _ _ = F
End

Definition itree_depth_eqv_def:
  itree_depth_eqv x y = ∀n. itree_eqn n x y
End

Theorem itree_eqn_refl:
  ∀n x. itree_eqn n x x
Proof
  Induct \\ Cases_on ‘x’ \\ rw[itree_eqn_def]
QED

Theorem itree_depth_eqv_eq:
  ∀x y. itree_depth_eqv x y ⇔ x = y
Proof
  rw[] \\ EQ_TAC \\ gs[itree_depth_eqv_def,itree_eqn_refl]
  \\ rw[Once itree_bisimulation]
  \\ qexists_tac ‘itree_depth_eqv’
  \\ rw[itree_depth_eqv_def]
  \\ Cases_on ‘t’ \\ gs[itree_eqn_def] \\ rw[]
  \\ pop_assum (qspec_then ‘SUC n’ assume_tac)
  \\ gs[itree_eqn_def]
QED

Theorem itree_eqn_trans:
  ∀n a b c.
    itree_eqn n a b ∧
    itree_eqn n b c ⇒
    itree_eqn n a c
Proof
  Induct_on ‘n’ \\ rw[itree_eqn_def]
  \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ Cases_on ‘c’
  \\ gs[itree_eqn_def] \\ metis_tac []
QED

Theorem itree_eqn_sym:
  ∀n a b. itree_eqn n a b ⇒ itree_eqn n b a
Proof
  Induct_on ‘n’ \\ rw[itree_eqn_def]
  \\ Cases_on ‘a’ \\ Cases_on ‘b’
  \\ gs[itree_eqn_def] \\ metis_tac []
QED

(* TODO: Give this equivalence better names *)

(* tidy up theory exports *)

val _ = List.app Theory.delete_binding
  ["Ret_rep_def", "Ret_def",
   "Tau_rep_def", "Tau_def",
   "Vis_rep_def", "Vis_def",
   "path_ok_def", "itree_rep_ok_def",
   "itree_unfold_path_def", "itree_unfold_path_ind",
   "itree_el_TY_DEF", "itree_absrep", "itree_next_TY_DEF"];

val _ = export_theory();
