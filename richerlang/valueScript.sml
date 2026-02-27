open HolKernel Parse boolLib bossLib
open fmaptreeTheory stringTheory finite_mapTheory;

val _ = new_theory "value";

Type value0 = “:(string, (num + string) + (bool + (string#α))) fmaptree”

Definition IntV0_def:
  IntV0 n = FTNode (INL (INL n)) FEMPTY :α value0
End

Definition StrV0_def:
  StrV0 s = FTNode (INL (INR s)) FEMPTY :α value0
End

Definition BoolV0_def:
  BoolV0 b = FTNode (INR (INL b)) FEMPTY :α value0
End

Definition Clos0_def:
  Clos0 s (e:α) E = FTNode (INR (INR (s, e))) E :α value0
End

Definition PairV0_def:
  PairV0 v1 v2 = FTNode (INL (INL 2)) (FEMPTY |+ ("", v1) |+ ("0", v2))
End

Definition SumV0_def:
  SumV0 (INL u) = FTNode (INL (INL 0)) (FEMPTY |+ ("", u)) ∧
  SumV0 (INR v) = FTNode (INL (INL 1)) (FEMPTY |+ ("", v))
End

Inductive is_value:
[~int:] ∀n. is_value (IntV0 n)
[~str:] ∀s. is_value (StrV0 s)
[~bool:] ∀b. is_value (BoolV0 b)
[~clos:] ∀s e E. (∀u v. FLOOKUP E u = SOME v ⇒ is_value v) ⇒
                 is_value (Clos0 s e E)
[~pair:] ∀v1 v2. is_value v1 ∧ is_value v2 ⇒ is_value (PairV0 v1 v2)
[~sumL:] ∀v. is_value v ⇒ is_value (SumV0 (INL v))
[~sumR:] ∀v. is_value v ⇒ is_value (SumV0 (INR v))
End

Theorem is_value_exists:
  ∃x. is_value x
Proof
  qexists ‘IntV0 0’>>simp[is_value_int]
QED

(*
val r = newtypeTools.rich_new_type {
  exthm = is_value_exists,
  tyname = "value",
  ABS = "value_ABS",
  REP = "value_REP"
  };
*)

val r = newtypeTools.rich_new_type ("value", is_value_exists);

Theorem is_value_Clos0[simp,local]:
  is_value (Clos0 s e (value_REP o_f E))
Proof
  irule is_value_clos >>
  simp[FLOOKUP_o_f, PULL_EXISTS, AllCaseEqs(), #termP_term_REP r]
QED

Definition IntV_def[nocompute]:
  IntV n = value_ABS (IntV0 n)
End

Definition StrV_def[nocompute]:
  StrV s = value_ABS (StrV0 s)
End

Definition BoolV_def[nocompute]:
  BoolV b = value_ABS (BoolV0 b)
End

Definition Clos_def[nocompute]:
  Clos s e E = value_ABS (Clos0 s e (value_REP o_f E))
End

Definition PairV_def[nocompute]:
  PairV v1 v2 = value_ABS (PairV0 (value_REP v1) (value_REP v2))
End

Definition SumLV_def[nocompute]:
  SumLV v = value_ABS (SumV0 (INL (value_REP v)))
End

Definition SumRV_def[nocompute]:
  SumRV v = value_ABS (SumV0 (INR (value_REP v)))
End
        
Theorem FORALL_value:
  (∀v. P v) ⇔ ∀v0. is_value v0 ⇒ P (value_ABS v0)
Proof
  simp[EQ_IMP_THM] >> rw[] >> pop_assum $ qspec_then ‘value_REP v’ mp_tac >>
  simp[#termP_term_REP r, #absrep_id r]
QED

Theorem value_ind:
  ∀P. (∀n. P (IntV n)) ∧ (∀s. P (StrV s)) ∧ (∀b. P (BoolV b)) ∧
      (∀v1 v2. P v1 ∧ P v2 ⇒ P (PairV v1 v2)) ∧
      (∀v. P v ⇒ P (SumLV v)) ∧ (∀v. P v ⇒ P (SumRV v)) ∧
      (∀s e E. (∀k v. FLOOKUP E k = SOME v ⇒ P v) ⇒ P (Clos s e E)) ⇒
      ∀v. P v
Proof
  gen_tac >> strip_tac >>
  simp[FORALL_value] >>
  Induct_on ‘is_value’ >> gvs[IntV_def, StrV_def, BoolV_def, PairV_def, SumLV_def, SumRV_def] >>
  gvs[Clos_def] >> rpt strip_tac >> gvs[FORALL_value] >~
  [‘P (value_ABS (Clos0 s e E))’]
  >- (first_x_assum $ qspecl_then [‘s’, ‘e’, ‘value_ABS o_f E’] mp_tac >>
      ‘value_REP o_f value_ABS o_f E = E’
        by (simp[FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_o_f, AllCaseEqs(), PULL_EXISTS] >>
            qx_gen_tac ‘k’ >> Cases_on ‘FLOOKUP E k’ >> simp[] >>
            metis_tac[#repabs_pseudo_id r]) >>
      simp[] >> disch_then irule >> simp[FLOOKUP_o_f, PULL_EXISTS, AllCaseEqs()] >>
      metis_tac[#term_ABS_pseudo11 r]) >>
  gvs[#repabs_pseudo_id r]
QED

Theorem value_ax:
  ∀intf sf bf 
  (pf : α value -> α value -> β -> β -> β)
  (slf : α value -> β -> β) (srf : α value -> β -> β)
  (cf : string -> α -> (string |-> α value) -> (string |-> β) -> β) .
    ∃h : α value -> β.
      (∀n. h (IntV n) = intf n) ∧
      (∀s. h (StrV s) = sf s) ∧
      (∀b. h (BoolV b) = bf b) ∧
      (∀v1 v2. h (PairV v1 v2) = pf v1 v2 (h v1) (h v2)) ∧
      (∀v. h (SumLV v) = slf v (h v)) ∧
      (∀v. h (SumRV v) = srf v (h v)) ∧
      (∀s e E. h (Clos s e E) = cf s e E (h o_f E))
Proof
  rpt strip_tac >>
  qexists ‘
    fmtreerec
    (λa r m. case a of
             | INL (INL n) => if m = FEMPTY then intf n
                              else if n = 2 then pf (value_ABS (m ' ""))
                                                    (value_ABS (m ' "0"))
                                                    (r ' "") (r ' "0")
                              else if n = 0 then slf (value_ABS (m ' "")) (r ' "")
                              else (* if n = 1 then *) srf (value_ABS (m ' "")) (r ' "")
             | INL (INR s) => sf s
             | INR (INL b) => bf b
             | INR (INR (s,e)) => cf s e (value_ABS o_f m) r) o value_REP’ >>
  rw[IntV_def, #repabs_pseudo_id r, is_value_rules, StrV_def, BoolV_def,
     Clos_def, PairV_def, SumLV_def, SumRV_def, #termP_term_REP r]
  >- simp[IntV0_def, fmtreerec_thm]
  >- simp[StrV0_def, fmtreerec_thm]
  >- simp[BoolV0_def, fmtreerec_thm]
  >- simp[PairV0_def, fmtreerec_thm, #absrep_id r, finite_mapTheory.FAPPLY_FUPDATE_THM]
  >- simp[SumV0_def, fmtreerec_thm, #absrep_id r, finite_mapTheory.FAPPLY_FUPDATE_THM]
  >- simp[SumV0_def, fmtreerec_thm, #absrep_id r, finite_mapTheory.FAPPLY_FUPDATE_THM] >>
  simp[Clos0_def, fmtreerec_thm] >>
  ‘value_ABS o value_REP = (λx. x)’ suffices_by simp[] >>
  simp[FUN_EQ_THM, #absrep_id r]
QED

val _ = TypeBase.export (
          TypeBasePure.gen_datatype_info{
            ax = value_ax,
            case_defs = Prim_rec.define_case_constant value_ax,
            ind = value_ind
          }
        );

Overload "case" = “value_CASE”

val gen_value_size_def =
 new_specification(
   "gen_value_size_def", ["gen_value_size"],
   value_ax |> INST_TYPE [beta |-> “:num”]
            |> Q.SPECL [‘λi. 1 + nsize i’, ‘λs. 1 + ssize s’, ‘λb. 1 + bsize b’,
                        ‘λv1 v2 n1 n2. 1 + n1 + n2’, ‘λv n. 1 + n’, ‘λv n. 1 + n’,
                        ‘λs e E r. ssize s + esize e + ITFMAP (K $+) r 0 + 1’]
            |> Q.GENL [‘nsize’, ‘ssize’, ‘bsize’, ‘esize’]
            |> SRULE[SKOLEM_THM]
 );

Overload value_size = “gen_value_size (K 0) (K 0) (K 0) (K 0)”

Theorem value_size_thm =
        gen_value_size_def |> Q.SPECL [‘K 0’, ‘K 0’, ‘K 0’, ‘K 0’] |> SRULE[]

Definition is_BoolV_def[simp]:
  is_BoolV (BoolV _) = T ∧
  is_BoolV _ = F
End

val _ = export_theory();
