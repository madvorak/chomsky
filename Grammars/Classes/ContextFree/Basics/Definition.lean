import Grammars.Classes.ContextSensitive.Basics.Definition


/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CFgrammar (T : Type) where
  nt : Type                              -- type of nonterminals
  initial : nt                           -- initial symbol
  rules : List (nt × List (Symbol T nt)) -- rewrite rules

variable {T : Type}

/-- One step of context-free transformation. -/
def CFgrammar.Transforms (g : CFgrammar T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : g.nt × List (Symbol T g.nt),
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ [Symbol.nonterminal r.fst] ++ v ∧ w₂ = u ++ r.snd ++ v

/-- Any number of steps of context-free transformation. -/
def CFgrammar.Derives (g : CFgrammar T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def CFgrammar.Generates (g : CFgrammar T) (w : List T) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def CFgrammar.Language (g : CFgrammar T) : Language T :=
  setOf g.Generates

/-- Predicate "is context-free"; defined by existence of a context-free grammar for the given language. -/
def IsCF (L : Language T) : Prop :=
  ∃ g : CFgrammar T, g.Language = L
