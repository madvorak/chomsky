import Chomsky.Classes.ContextFree.Basics.Definition

variable {T : Type} {g : CFG T}


/-- The relation `CFG.Derives` is reflexive. -/
lemma CFG.deri_self {w : List (Symbol T g.nt)} :
  g.Derives w w :=
Relation.ReflTransGen.refl

lemma CFG.deri_of_tran {v w : List (Symbol T g.nt)} (ass : g.Transforms v w) :
  g.Derives v w :=
Relation.ReflTransGen.single ass

/-- The relation `CFG.Derives` is transitive. -/
lemma CFG.deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
  g.Derives u w :=
Relation.ReflTransGen.trans huv hvw

lemma CFG.deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Transforms v w) :
  g.Derives u w :=
CFG.deri_of_deri_deri huv (CFG.deri_of_tran hvw)

lemma CFG.deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Transforms u v) (hvw : g.Derives v w) :
  g.Derives u w :=
CFG.deri_of_deri_deri (CFG.deri_of_tran huv) hvw

lemma CFG.eq_or_tran_deri_of_deri {u w : List (Symbol T g.nt)} (ass : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
Relation.ReflTransGen.cases_head ass

lemma CFG.eq_or_deri_tran_of_deri {u w : List (Symbol T g.nt)} (ass : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Derives u v ∧ g.Transforms v w  :=
(Relation.ReflTransGen.cases_tail ass).casesOn (Or.inl ∘ Eq.symm) Or.inr


lemma CFG.deri_with_prefix {w₁ w₂ : List (Symbol T g.nt)}
    (pᵣ : List (Symbol T g.nt)) (ass : g.Derives w₁ w₂) :
  g.Derives (pᵣ ++ w₁) (pᵣ ++ w₂) :=
by
  induction' ass with a b _ hyp ih
  · apply CFG.deri_self
  apply CFG.deri_of_deri_tran
  · exact ih
  rcases hyp with ⟨r, r_in, v, w, h_bef, h_aft⟩
  use r
  constructor
  · exact r_in
  use pᵣ ++ v
  use w
  rw [h_bef]
  rw [h_aft]
  constructor <;> simp only [List.append_assoc]

lemma CFG.deri_with_postfix {w₁ w₂ : List (Symbol T g.nt)}
    (pₒ : List (Symbol T g.nt)) (ass : g.Derives w₁ w₂) :
  g.Derives (w₁ ++ pₒ) (w₂ ++ pₒ) :=
by
  induction' ass with a b _ hyp ih
  · apply CFG.deri_self
  apply CFG.deri_of_deri_tran
  · exact ih
  rcases hyp with ⟨r, r_in, v, w, h_bef, h_aft⟩
  use r
  constructor
  · exact r_in
  use v
  use w ++ pₒ
  rw [h_bef]
  rw [h_aft]
  constructor <;> simp only [List.append_assoc]
