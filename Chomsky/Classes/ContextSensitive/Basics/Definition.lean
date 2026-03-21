import Chomsky.Classes.Unrestricted.Basics.Definition
import Mathlib.Logic.Relation

/-- Rewrite rule for a context-sensitive grammar. -/
structure CSRule (T N : Type) where
  contextL : List (Symbol T N)
  inputN : N
  contextR : List (Symbol T N)
  output : List (Symbol T N)

/-- Context-sensitive grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CSG (T : Type) where
  nt : Type                 -- type of nonterminals
  initial : nt              -- initial symbol
  rules : List (CSRule T nt) -- rewrite rules

variable {T : Type}

/-- One step of context-sensitive transformation. -/
def CSG.Transforms (g : CSG T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : CSRule T g.nt,
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ r.contextL ++ [Symbol.nonterminal r.inputN] ++ r.contextR ++ v ∧
      w₂ = u ++ r.contextL ++ r.output ++ r.contextR ++ v

/-- Any number of steps of context-sensitive transformation. -/
def CSG.Derives (g : CSG T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- The set of words that can be derived from the initial nonterminal. -/
def CSG.language (g : CSG T) : Language T :=
  { w : List T | g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) }

/-- Predicate "is context-sensitive"; defined by existence of a context-sensitive grammar for the given language. -/
def Language.IsCS (L : Language T) : Prop :=
  ∃ g : CSG T, g.language = L
