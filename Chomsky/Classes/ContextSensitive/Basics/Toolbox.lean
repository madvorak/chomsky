import Chomsky.Classes.ContextSensitive.Basics.Definition

variable {T : Type} {g : CSG T}


/-- The relation `CSG.Derives` is reflexive. -/
lemma CSG.deri_self {w : List (Symbol T g.nt)} :
  g.Derives w w :=
Relation.ReflTransGen.refl

lemma CSG.deri_of_tran {v w : List (Symbol T g.nt)} (ass : g.Transforms v w) :
  g.Derives v w :=
Relation.ReflTransGen.single ass

/-- The relation `CSG.Derives` is transitive. -/
lemma CSG.deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
  g.Derives u w :=
Relation.ReflTransGen.trans huv hvw

lemma CSG.deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Transforms v w) :
  g.Derives u w :=
CSG.deri_of_deri_deri huv (CSG.deri_of_tran hvw)

lemma CSG.deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Transforms u v) (hvw : g.Derives v w) :
  g.Derives u w :=
CSG.deri_of_deri_deri (CSG.deri_of_tran huv) hvw

lemma CSG.eq_or_tran_deri_of_deri {u w : List (Symbol T g.nt)} (ass : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
Relation.ReflTransGen.cases_head ass

lemma CSG.eq_or_deri_tran_of_deri {u w : List (Symbol T g.nt)} (ass : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Derives u v ∧ g.Transforms v w  :=
(Relation.ReflTransGen.cases_tail ass).casesOn (Or.inl ∘ Eq.symm) Or.inr
