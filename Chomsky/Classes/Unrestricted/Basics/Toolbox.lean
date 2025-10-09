import Chomsky.Classes.Unrestricted.Basics.Definition

variable {T : Type} {g : Grammar T}


/-- The relation `Grammar.derives` is reflexive. -/
lemma Grammar.deri_self {w : List (Symbol T g.nt)} :
  g.Derives w w :=
Relation.ReflTransGen.refl

lemma Grammar.deri_of_tran {v w : List (Symbol T g.nt)}
    (hgvw : g.Transforms v w) :
  g.Derives v w :=
Relation.ReflTransGen.single hgvw

/-- The relation `Grammar.derives` is transitive. -/
lemma Grammar.deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (hguv : g.Derives u v) (hgvw : g.Derives v w) :
  g.Derives u w :=
Relation.ReflTransGen.trans hguv hgvw

lemma Grammar.deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (hguv : g.Derives u v) (hgvw : g.Transforms v w) :
  g.Derives u w :=
Grammar.deri_of_deri_deri hguv (Grammar.deri_of_tran hgvw)

lemma Grammar.deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (hguv : g.Transforms u v) (hgvw : g.Derives v w) :
  g.Derives u w :=
Grammar.deri_of_deri_deri (Grammar.deri_of_tran hguv) hgvw

lemma Grammar.eq_or_tran_deri_of_deri {u w : List (Symbol T g.nt)} (hguw : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
Relation.ReflTransGen.cases_head hguw

lemma Grammar.eq_or_deri_tran_of_deri {u w : List (Symbol T g.nt)} (hguw : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Derives u v ∧ g.Transforms v w  :=
(Relation.ReflTransGen.cases_tail hguw).casesOn (Or.inl ∘ Eq.symm) Or.inr


lemma Grammar.append_deri {w₁ w₂ : List (Symbol T g.nt)}
    (pᵣ : List (Symbol T g.nt)) (hgww : g.Derives w₁ w₂) :
  g.Derives (pᵣ ++ w₁) (pᵣ ++ w₂) :=
by
  induction' hgww with x y _ hgxy ih
  · apply Grammar.deri_self
  apply Grammar.deri_of_deri_tran
  · exact ih
  rcases hgxy with ⟨r, rin, u, v, h_bef, h_aft⟩
  use r
  constructor
  · exact rin
  use pᵣ ++ u, v
  rw [h_bef, h_aft]
  constructor <;> simp only [List.append_assoc]

lemma Grammar.deri_append {w₁ w₂ : List (Symbol T g.nt)}
    (pₒ : List (Symbol T g.nt)) (hgww : g.Derives w₁ w₂) :
  g.Derives (w₁ ++ pₒ) (w₂ ++ pₒ) :=
by
  induction' hgww with x y _ hgxy ih
  · apply Grammar.deri_self
  apply Grammar.deri_of_deri_tran
  · exact ih
  rcases hgxy with ⟨r, rin, u, v, h_bef, h_aft⟩
  use r
  constructor
  · exact rin
  use u, v ++ pₒ
  rw [h_bef, h_aft]
  constructor <;> simp only [List.append_assoc]


def asTerminal {N : Type} : Symbol T N → Option T
  | Symbol.terminal t => some t
  | Symbol.nonterminal _ => none

def allUsedTerminals (g : Grammar T) : List T :=
  ((g.rules.map Grule.output).flatten).filterMap asTerminal
