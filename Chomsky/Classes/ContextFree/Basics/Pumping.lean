import Chomsky.Classes.ContextFree.Basics.Definition
import Chomsky.Utilities.ListUtils

/-- Pumping lemma for context-free languages. -/
lemma Language.IsCF.pumping {T : Type} {L : Language T} (cf : L.IsCF) :
  ∃ n : ℕ, ∀ w ∈ L, w.length ≥ n → ∃ u v x y z : List T,
    w = u ++ v ++ x ++ y ++ z ∧
    (v ++ y).length > 0       ∧
    (v ++ x ++ y).length ≤ n  ∧
    ∀ i : ℕ, u ++ v ^^ i ++ x ++ y ^^ i ++ z ∈ L :=
sorry
