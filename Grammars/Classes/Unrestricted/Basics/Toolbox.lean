import Grammars.Classes.Unrestricted.Basics.Definition

variable {T : Type} {g : Grammar T}


/-- The relation `Grammar.derives` is reflexive. -/
lemma Grammar.deri_self {w : List (Symbol T g.nt)} :
  g.Derives w w :=
Relation.ReflTransGen.refl

lemma Grammar.deri_of_tran {v w : List (Symbol T g.nt)}
    (ass : g.Transforms v w) :
  g.Derives v w :=
Relation.ReflTransGen.single ass

/-- The relation `Grammar.derives` is transitive. -/
lemma Grammar.deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
  g.Derives u w :=
Relation.ReflTransGen.trans huv hvw

lemma Grammar.deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Transforms v w) :
  g.Derives u w :=
Grammar.deri_of_deri_deri huv (Grammar.deri_of_tran hvw)

lemma Grammar.deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Transforms u v) (hvw : g.Derives v w) : 
  g.Derives u w :=
Grammar.deri_of_deri_deri (Grammar.deri_of_tran huv) hvw

lemma Grammar.tran_or_id_of_deri {u w : List (Symbol T g.nt)}
    (ass : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
Relation.ReflTransGen.cases_head ass


lemma Grammar.deri_with_prefix {w₁ w₂ : List (Symbol T g.nt)}
    (pᵣ : List (Symbol T g.nt)) (ass : g.Derives w₁ w₂) :
  g.Derives (pᵣ ++ w₁) (pᵣ ++ w₂) :=
by
  induction' ass with x y _ hyp ih
  · apply Grammar.deri_self
  apply Grammar.deri_of_deri_tran
  · exact ih
  rcases hyp with ⟨r, rin, u, v, h_bef, h_aft⟩
  use r
  constructor
  · exact rin
  use pᵣ ++ u
  use v
  rw [h_bef]
  rw [h_aft]
  constructor <;> simp only [List.append_assoc]

lemma Grammar.deri_with_postfix {w₁ w₂ : List (Symbol T g.nt)}
    (pₒ : List (Symbol T g.nt)) (ass : g.Derives w₁ w₂) :
  g.Derives (w₁ ++ pₒ) (w₂ ++ pₒ) :=
by
  induction' ass with x y _ hyp ih
  · apply Grammar.deri_self
  apply Grammar.deri_of_deri_tran
  · exact ih
  rcases hyp with ⟨r, rin, u, v, h_bef, h_aft⟩
  use r
  constructor
  · exact rin
  use u
  use v ++ pₒ
  rw [h_bef]
  rw [h_aft]
  constructor <;> simp only [List.append_assoc]


def asTerminal {N : Type} : Symbol T N → Option T
  | Symbol.terminal t => some t
  | Symbol.nonterminal _ => none

def allUsedTerminals (g : Grammar T) : List T :=
  List.filterMap asTerminal (List.join (List.map Grule.outputString g.rules))
