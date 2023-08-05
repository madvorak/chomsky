import Grammars.Classes.Unrestricted.Basics.Definition

/-- Rewrite rule for a context-sensitive grammar. -/
structure CSrule (T : Type) (N : Type) where
  contextLeft : List (Symbol T N)
  inputNonterminal : N
  contextRight : List (Symbol T N)
  outputString : List (Symbol T N)
  output_nonempty : outputString.length > 0

/-- Context-sensitive grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CSgrammar (T : Type) where
  nt : Type                  -- type of nonterminals
  initial : nt               -- initial symbol
  rules : List (CSrule T nt) -- rewrite rules
  allow_empty : Bool         -- whether empty word can be generated

variable {T : Type}

/-- One step of context-sensitive transformation. -/
def CSgrammar.Transforms (g : CSgrammar T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : CSrule T g.nt,
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ r.contextLeft ++ [Symbol.nonterminal r.inputNonterminal] ++ r.contextRight ++ v ∧
      w₂ = u ++ r.contextLeft ++ r.outputString ++ r.contextRight ++ v

/-- Any number of steps of context-sensitive transformation. -/
def CSgrammar.Derives (g : CSgrammar T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

def CSgrammar.Generates (g : CSgrammar T) (w : List T) : Prop :=
  (w = [] ∧ g.allow_empty) ∨
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)

def CSgrammar.language (g : CSgrammar T) : Language T :=
  setOf g.Generates

/-- Predicate "is context-sensitive"; defined by existence of a context-sensitive grammar for the given language. -/
def IsCS (L : Language T) : Prop :=
  ∃ g : CSgrammar T, g.language = L
