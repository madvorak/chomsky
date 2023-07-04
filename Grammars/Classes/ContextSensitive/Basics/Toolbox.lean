import Grammars.Classes.ContextSensitive.Basics.Definition

variable {T : Type} {g : CSgrammar T}


/-- The relation `CS_derives` is reflexive. -/
lemma CSgrammar.deri_self {w : List (Symbol T g.nt)} :
  g.Derives w w :=
Relation.ReflTransGen.refl

lemma CSgrammar.deri_of_tran {v w : List (Symbol T g.nt)} (ass : g.Transforms v w) :
  g.Derives v w :=
Relation.ReflTransGen.single ass

/-- The relation `CS_derives` is transitive. -/
lemma CSgrammar.deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
  g.Derives u w :=
Relation.ReflTransGen.trans huv hvw

lemma CSgrammar.deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Transforms v w) :
  g.Derives u w :=
CSgrammar.deri_of_deri_deri huv (CSgrammar.deri_of_tran hvw)

lemma CSgrammar.deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Transforms u v) (hvw : g.Derives v w) :
  g.Derives u w :=
CSgrammar.deri_of_deri_deri (CSgrammar.deri_of_tran huv) hvw

lemma CSgrammar.tran_or_id_of_deri {u w : List (Symbol T g.nt)} (ass : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
Relation.ReflTransGen.cases_head ass
