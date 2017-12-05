open preamble

open astBakeryTheory

val _ = new_theory "typeBakery";

val _ = Datatype`
              (* Comunication : A -> B  ; G *)
  bakery_type = TCom proc proc bakery_type
              (* Selection : A -> B ; {T : G₁, F : G₂} *)
              | TSel proc proc bakery_type bakery_type
              (* End *)
              | TEnd
`;

val _ = Datatype`
  type_tag = τCom proc proc
           | τSel proc proc bool
`;

val roles_def = Define`
  roles (τCom a b)   = {a;b}
∧ roles (τSel a b _) = {a;b}
`;

val (type_rules,type_ind,type_cases) = Hol_reln `

  (* Comunication *)
  (∀a b g. type_sem (TCom a b g) (τCom a b) g)

  (* Selection for true branch*)
∧ (∀a b g1 g2. type_sem (TSel a b g1 g2) (τSel a b T) g1)

  (* Selection for false branch *)
∧ (∀a b g1 g2. type_sem (TSel a b g1 g2) (τSel a b F) g2)

  (* Swapping transitions *)
∧ (∀a b g1 g2 g1' g2' α .
    type_sem g1 α g1'
    ∧ type_sem g2 α g2'
    ∧ {a;b} ∩ roles α = ∅
    ⇒ type_sem (TSel a b g1 g2) α (TSel a b g1' g2'))

∧ (∀a b g g' α .
    type_sem g α g'
    ∧ {a;b} ∩ roles α = ∅
    ⇒ type_sem (TCom a b g) α (TCom a b g'))

  (* Asyncrony *)
∧ (∀a b g1 g2 g1' g2' α .
    type_sem g1 α g1'
    ∧ type_sem g2 α g2'
    ∧ a ∈ roles α
    ∧ b ∉ roles α
    ⇒ type_sem (TSel a b g1 g2) α (TSel a b g1' g2'))

∧ (∀a b g g' α .
    type_sem g α g'
    ∧ a ∈ roles α
    ∧ b ∉ roles α
    ⇒ type_sem (TCom a b g) α (TCom a b g'))
`;

val (chortype_rules,chortype_ind,chortype_cases) = Hol_reln `
  (* Nil *)
  (chortype Nil TEnd)
  (* Comunication *)
∧ (∀p v q x c g.
    chortype c g
    ⇒ chortype (Com p v q x c) (TCom p q g))

  (* Selection (true) *)
∧ (∀p q c g1 g2.
    chortype c g1
    ⇒ chortype (Sel p T q c) (TSel p q g1 g2))

  (* Selection (false) *)
∧ (∀p q c g1 g2.
    chortype c g2
    ⇒ chortype (Sel p F q c) (TSel p q g1 g2))

  (* Let *)
∧ (∀v p f vl c g.
    chortype c g
    ⇒ chortype (Let v p f vl c) g)

  (* If *)
∧ (∀v p c1 c2 g.
    chortype c1 g
    ∧ chortype c1 g
    ⇒ chortype (IfThen v p c1 c2) g)
`;

val _ = export_theory ()
