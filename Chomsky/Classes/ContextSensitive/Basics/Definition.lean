import Chomsky.Classes.Unrestricted.Basics.Definition


/-- Rewrite rule for a context-sensitive grammar. -/
structure CSR (T : Type) (N : Type) where
  contextLeft : List (Symbol T N)
  inputNonterminal : N
  contextRight : List (Symbol T N)
  outputString : List (Symbol T N)
  output_nonempty : outputString.length > 0

/-- Context-sensitive grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CSG (T : Type) where
  nt : Type                  -- type of nonterminals
  initial : nt               -- initial symbol
  rules : List (CSR T nt) -- rewrite rules
  allow_empty : Bool         -- whether empty word can be generated

variable {T : Type}

/-- One step of context-sensitive transformation. -/
def CSG.Transforms (g : CSG T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : CSR T g.nt,
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ r.contextLeft ++ [Symbol.nonterminal r.inputNonterminal] ++ r.contextRight ++ v ∧
      w₂ = u ++ r.contextLeft ++ r.outputString ++ r.contextRight ++ v

/-- Any number of steps of context-sensitive transformation. -/
def CSG.Derives (g : CSG T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- The set of words that can be derived from the initial nonterminal. -/
def CSG.language (g : CSG T) : Language T :=
  { w : List T | w = [] ∧ g.allow_empty ∨
                 g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) }

/-- Predicate "is context-sensitive"; defined by existence of a context-sensitive grammar for the given language. -/
def Language.IsCS (L : Language T) : Prop :=
  ∃ g : CSG T, g.language = L
