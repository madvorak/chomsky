import Grammars.Classes.ContextFree.Basics.Definition
import Grammars.Utilities.ListUtils

/-- Pumping lemma for context-free languages. -/
lemma CF_pumping {T : Type} {L : Language T} (cf : IsCF L) :
  ∃ n : ℕ, ∀ w ∈ L, List.length w ≥ n → ∃ u v x y z : List T,
    w = u ++ v ++ x ++ y ++ z  ∧
    (v ++ y).length > 0        ∧
    (v ++ x ++ y).length ≤ n   ∧
    ∀ i : ℕ, u ++ v ^^ i ++ x ++ y ^^ i ++ z ∈ L :=
sorry

