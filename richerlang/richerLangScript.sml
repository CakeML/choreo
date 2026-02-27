open HolKernel Parse boolLib bossLib stringTheory listTheory numposrepTheory arithmeticTheory finite_mapTheory numstringTheory valueTheory; 

val _ = new_theory "richerLang";

val _ = hide "STRING";

val _ = monadsyntax.enable_monadsyntax();

val _ = hide "env";

Datatype:
  bop = Add | Concat | Mult | Div | Mod | Less | And | Or | Eq | Sub | Pair
End

Datatype:
  uop = Not | NumOf | StrOf | Fst | Snd | SumL | SumR
End

Datatype:
  type = intT | strT | boolT | fnT type type | pairT type type | sumT type type
End        
    
Datatype:
  exp = Var string
  | StrLit string
  | IntLit num
  | BoolLit bool
  | BinOp bop exp exp
  | Uop uop exp
  | If exp exp exp
  | Let string exp exp
  | Fn string exp
  | App exp exp
  | Case exp string exp string exp
End

Datatype:
  exn = Div0 | BadStr
End

Datatype:
  result = Value α | TypeError | Exn exn | Timeout
End

(* Type env = “:string |-> value” *)

Definition result_bind_def[simp]:
  result_bind (Value v) f = f v ∧
  result_bind TypeError f = TypeError ∧
  result_bind (Exn e) f = Exn e ∧
  result_bind Timeout f = Timeout
End

val _ = monadsyntax.declare_monad("result", {bind = “result_bind”, ignorebind = NONE,
                                  unit = “Value”, fail = NONE, choice = NONE, guard = NONE});

val _ = monadsyntax.enable_monad"result";                                  

Definition getI_def[simp]:
  getI (IntV n) = return n ∧
  getI _ = TypeError
End

Definition getS_def[simp]:
  getS (StrV s) = return s ∧
  getS _ = TypeError
End

Definition getB_def[simp]:
  getB (BoolV b) = return b ∧
  getB _ = TypeError
End

Theorem getB_EQ_value[simp]:
  ∀ vv v. getB vv = Value v ⇔ vv = BoolV v                          
Proof
  Cases_on ‘vv’ >> simp[]
QED

Definition getP_def[simp]:
  getP (PairV v1 v2) = return (v1, v2) ∧
  getP _ = TypeError
End

Definition binIop_def:
  binIop f v1 v2 =
  do
    i1 <- getI v1;
    i2 <- getI v2;
    return $ IntV $ f i1 i2;
  od
End

Definition binSop_def:
  binSop f v1 v2 =
  do
    s1 <- getS v1;
    s2 <- getS v2;
    return $ StrV $ f s1 s2;
  od
End

Definition binBop_def:
  binBop f v1 v2 =
  do
    b1 <- getB v1;
    b2 <- getB v2;
    return $ BoolV $ f b1 b2;
  od
End

Definition eval_bop_def:
  eval_bop Add v1 v2 = binIop (+) v1 v2 ∧
  eval_bop Concat v1 v2 = binSop (++) v1 v2 ∧
  eval_bop Mult v1 v2 = binIop ($*) v1 v2 ∧
  eval_bop Div v1 v2 = (if (getI v2 ≠ return 0) then binIop (DIV) v1 v2 else Exn Div0) ∧
  eval_bop Mod v1 v2 = (if (getI v2 ≠ return 0) then binIop (MOD) v1 v2 else Exn Div0) ∧
  eval_bop Less v1 v2 =
  do
    i1 <- getI v1;
    i2 <- getI v2;
    return $ BoolV $ (<) i1 i2;
  od ∧
  eval_bop And v1 v2 = binBop (/\) v1 v2 ∧
  eval_bop Or v1 v2 = binBop (\/) v1 v2 ∧
  eval_bop Eq v1 v2 = return $ BoolV $ (v1=v2) ∧
  eval_bop Sub v1 v2 = binIop (-) v1 v2 ∧
  eval_bop Pair v1 v2 = return (PairV v1 v2)
End

Definition eval_uop_def:
  eval_uop Not v =
  do
    b <- getB v;
    return $ BoolV $ ~b;
  od ∧
  eval_uop NumOf v =
  do
    s <- getS v;
    case string_to_int2 s of
      NONE => Exn BadStr
    | SOME i => return $ IntV $ i;
  od ∧
  eval_uop StrOf v =
  do
    i <- getI v;
    return $ StrV $ int_to_string i;
  od ∧
  eval_uop Fst v =
  do
    v <- getP v;
    return (FST v);
  od ∧
  eval_uop Snd v =
  do
    v <- getP v;
    return (SND v);
  od ∧
  eval_uop SumL v = return (SumLV v) ∧
  eval_uop SumR v = return (SumRV v)
End


Inductive uoptype:
[~not:] uoptype Not boolT boolT
[~s2i:] uoptype NumOf strT intT
[~i2s:] uoptype StrOf intT strT
[~fst:] ∀ t1 t2. uoptype Fst (pairT t1 t2) t1
[~snd:] ∀ t1 t2. uoptype Snd (pairT t1 t2) t2
[~suml:] ∀ t1 t2. uoptype SumL t1 (sumT t1 t2)
[~sumr:] ∀ t1 t2. uoptype SumR t2 (sumT t1 t2)
End

Inductive boptype:
[~bint:] ∀ bop. bop ∈ {Add;Mult;Div;Mod;Sub} ⇒ boptype bop intT intT intT
[~concat:] boptype Concat strT strT strT
[~Less:] boptype Less intT intT boolT
[~Eq:] ∀ t1 t2. boptype Eq t1 t2 boolT
[~pair:] ∀ t1 t2. boptype Pair t1 t2 (pairT t1 t2)
End
        
Inductive typecheck:
[~var:] ∀G x ty. FLOOKUP G x = SOME ty ⇒ typecheck G (Var x) ty
[~if:] ∀G e1 e2 e3 ty. typecheck G e1 boolT ∧ typecheck G e2 ty ∧ typecheck G e3 ty ⇒
                       typecheck G (If e1 e2 e3) ty
[~StrLit:] ∀G s. typecheck G (StrLit s) strT
[~IntLit:] ∀G n. typecheck G (IntLit n) intT
[~BoolLit:] ∀G b. typecheck G (BoolLit b) boolT
[~Binop:] ∀G bop e1 e2 ty t1 t2. boptype bop t1 t2 ty ∧ typecheck G e1 t1 ∧ typecheck G e2 t2 ⇒
                                 typecheck G (BinOp bop e1 e2) ty
[~Uop:] ∀G uop e t ty. uoptype uop t ty ∧ typecheck G e t ⇒ typecheck G (Uop uop e) ty
[~let:] ∀G s e1 e2 ty ety. typecheck G e1 ety ∧ typecheck (G |+ (s, ety)) e2 ty ⇒
                           typecheck G (Let s e1 e2) ty
[~fn:] ∀G s e t ty. typecheck (G |+ (s, t)) e ty ⇒ typecheck G (Fn s e) (fnT t ty)
[~app:] ∀G e1 e2 t ty. typecheck G e1 (fnT t ty) ∧ typecheck G e2 t ⇒ typecheck G (App e1 e2) ty
[~case:] ∀G e s1 e1 s2 e2 t1 t2 ty. typecheck G e (sumT t1 t2) ∧ typecheck (G |+ (s1, t1)) e1 ty ∧ typecheck (G |+ (s2, t2)) e2 ty ⇒ typecheck G (Case e s1 e1 s2 e2) ty
End

Theorem typecheck_var_thm[simp]:
  typecheck G (Var x) ty ⇔ FLOOKUP G x = SOME ty
Proof
  simp[Once typecheck_cases]
QED

Theorem typecheck_strlit_thm[simp]:
  typecheck G (StrLit s) ty ⇔ ty = strT
Proof
  simp[Once typecheck_cases]
QED

Theorem typecheck_intlit_thm[simp]:
  typecheck G (IntLit n) ty ⇔ ty = intT
Proof
  simp[Once typecheck_cases]
QED

Theorem typecheck_boollit_thm[simp]:
  typecheck G (BoolLit b) ty ⇔ ty = boolT
Proof
  simp[Once typecheck_cases]
QED

Theorem typecheck_binop_thm[simp] =
        typecheck_cases |> Q.SPECL [‘G’, ‘BinOp bop e1 e2’, ‘ty’] |> SRULE[]

Theorem typecheck_uop_thm[simp] =
        typecheck_cases |> Q.SPECL [‘G’, ‘Uop uop e’, ‘ty’] |> SRULE[]

Theorem typecheck_if_thm[simp] =
        typecheck_cases |> Q.SPECL [‘G’, ‘If e1 e2 e3’, ‘ty’] |> SRULE[]

Theorem typecheck_let_thm[simp] =
        typecheck_cases |> Q.SPECL [‘G’, ‘Let s e1 e2’, ‘ty’] |> SRULE[]

Theorem typecheck_fn_thm[simp] =
        typecheck_cases |> Q.SPECL [‘G’, ‘Fn s e’, ‘ty’] |> SRULE[]

Theorem typecheck_app_thm[simp] =
        typecheck_cases |> Q.SPECL [‘G’, ‘App e1 e2’, ‘ty’] |> SRULE[]

Theorem typecheck_case_thm[simp] =
        typecheck_cases |> Q.SPECL [‘G’, ‘Case e s1 e1 s2 e2’, ‘ty’] |> SRULE[]

Definition free_vars[simp]:
  free_vars (Var s) = {s} ∧
  free_vars (BinOp bop e1 e2) = free_vars e1 ∪ free_vars e2 ∧
  free_vars (Uop uop e) = free_vars e ∧
  free_vars (If e1 e2 e3) = free_vars e1 ∪ free_vars e2 ∪ free_vars e3 ∧
  free_vars (Let s e1 e2) = free_vars e1 ∪ (free_vars e2 DIFF {s}) ∧
  free_vars (Fn s e) = free_vars e DIFF {s} ∧
  free_vars (App e1 e2) = free_vars e1 ∪ free_vars e2 ∧
  free_vars (Case e s1 e1 s2 e2) = free_vars e ∪ (free_vars e1 DIFF {s1}) ∪ (free_vars e2 DIFF {s2}) ∧
  free_vars _ = {}
End

Theorem typecheck_vars:
  ∀ G e ty. typecheck G e ty ⇒ free_vars e ⊆ FDOM G
Proof
  Induct_on ‘typecheck’>> rw[] >> gvs[flookup_thm] >> ASM_SET_TAC []
QED

Inductive value_type:
[~IntV[simp]:] ∀ n. value_type (IntV n) intT
[~StrV[simp]:] ∀ s. value_type (StrV s) strT
[~BoolV[simp]:] ∀ b. value_type (BoolV b) boolT
[~FnV:] ∀ s e t1 t2 E G. (∀ str ty. FLOOKUP G str = SOME ty ⇒
                                    ∃ v. FLOOKUP E str = SOME v ∧ value_type v ty) ∧
                         typecheck (G|+(s, t1)) e t2 ⇒
                         value_type (Clos s e E) (fnT t1 t2)
[~PairV[simp]:] ∀ v1 v2 t1 t2. value_type v1 t1 ∧ value_type v2 t2 ⇒ value_type (PairV v1 v2) (pairT t1 t2)
[~SumLV[simp]:] ∀ v t1 t2. value_type v t1 ⇒ value_type (SumLV v) (sumT t1 t2)
[~SumRV[simp]:] ∀ v t1 t2. value_type v t2 ⇒ value_type (SumRV v) (sumT t1 t2)
End

Definition envtype_def:
  envtype G E = ∀ str ty. FLOOKUP G str = SOME ty ⇒
                          ∃ v. FLOOKUP E str = SOME v ∧ value_type v ty
End

Theorem envtype_lemma:
  ∀ v ty. value_type v ty ⇒
          ∀ G E s. envtype G E ⇒
                   envtype (G |+ (s, ty)) (E |+ (s, v))
Proof
  Induct_on ‘value_type’>>
  rw[envtype_def, FLOOKUP_UPDATE]>>rw[]>>simp[]>>gvs[]>>
  irule value_type_FnV>>metis_tac []
QED

Theorem valuetype_EQ_intT:
  ∀ v. value_type v intT ⇔
         ∃ n. v = IntV n
Proof
  simp[Once value_type_cases]
QED

Theorem valuetype_EQ_strT:
  ∀ v. value_type v strT ⇔
         ∃ s. v = StrV s
Proof
  simp[Once value_type_cases]
QED

Theorem valuetype_EQ_boolT:
  ∀ v. value_type v boolT ⇔
         ∃ b. v = BoolV b
Proof
  simp[Once value_type_cases]
QED

Theorem valuetype_EQ_fnT:
  ∀ v. value_type v (fnT ty1 ty2) ⇔
         ∃ s e E G. v = Clos s e E ∧ envtype G E ∧ typecheck (G|+(s, ty1)) e ty2
Proof
  simp[Once value_type_cases, envtype_def]
QED

Theorem valuetype_EQ_pairT:
  ∀ v t1 t2. value_type v (pairT t1 t2) ⇔
               ∃ v1 v2. v = (PairV v1 v2) ∧ value_type v1 t1 ∧ value_type v2 t2
Proof
  simp[Once value_type_cases]
QED

Theorem valuetype_EQ_sumT:
  ∀ v t1 t2. value_type v (sumT t1 t2) ⇔
             ∃ v0. v = SumLV v0 ∧ value_type v0 t1 ∨ v = SumRV v0 ∧ value_type v0 t2
Proof
  rpt strip_tac >> iff_tac >- rw[Once value_type_cases]
  >> strip_tac >> simp[]
QED

Theorem bop_type_soundness:
  ∀ bop v1 v2 ty. value_type v1 t1 ∧ value_type  v2 t2 ∧ boptype bop t1 t2 ty ⇒
                  (∃ v. eval_bop bop v1 v2 = Value v ∧ value_type v ty) ∨
                  (∃ e. eval_bop bop v1 v2 = Exn e)
Proof 
  rw[boptype_cases]>> gvs[valuetype_EQ_boolT, valuetype_EQ_strT, valuetype_EQ_intT, PULL_EXISTS, eval_bop_def, binIop_def, binSop_def, AllCaseEqs()]
QED

Theorem uop_type_soundness:
  ∀ uop v ty. value_type v t1 ∧ uoptype uop t1 ty ⇒
              (∃ v'. eval_uop uop v = Value v' ∧ value_type v' ty) ∨
              (∃ e. eval_uop uop v = Exn e)
Proof
  rw[uoptype_cases]
  >- ( (* NOT *) gvs[valuetype_EQ_boolT, PULL_EXISTS, eval_uop_def, result_bind_def])
  >- ( (* NumOf *) gvs[valuetype_EQ_strT, PULL_EXISTS, eval_uop_def, result_bind_def]>> Cases_on ‘string_to_int2 s’ >> simp[])
  >> gvs[valuetype_EQ_intT, valuetype_EQ_pairT, PULL_EXISTS, eval_uop_def, result_bind_def]
QED

val _ = export_theory();
