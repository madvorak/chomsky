import Chomsky.Classes.ContextFree.Basics.Definition

/-- Right-linear rule for a regular grammar. -/
inductive RLRule (T N : Type)
  | terminal : N → T → RLRule T N
  | nonterminal : N → T → N → RLRule T N
  | empty : N → RLRule T N

/-- Right-linear grammar that generates words over the alphabet `T` (a type of terminals). -/
structure RLG (T : Type) where
  nt : Type                 -- type of nonterminals
  initial : nt              -- initial symbol
  rules : List (RLRule T nt) -- rewrite rules

variable {T : Type}

/-- Convert a right-linear rule to a context-free rule. -/
def RLRule.toCF (r : RLRule T N) : N × List (Symbol T N) :=
  match r with
  | RLRule.terminal n t => (n, [Symbol.terminal t])
  | RLRule.nonterminal n t n' => (n, [Symbol.terminal t, Symbol.nonterminal n'])
  | RLRule.empty n => (n, [])

/-- Convert a right-linear grammar to a context-free grammar. -/
def RLG.toCFG (g : RLG T) : CFG T where
  nt := g.nt
  initial := g.initial
  rules := g.rules.map RLRule.toCF

/-- The language of a right-linear grammar is the language of its context-free counterpart. -/
def RLG.language (g : RLG T) : Language T :=
  g.toCFG.language

/-- Predicate "is regular"; defined by existence of a right-linear grammar for the given language. -/
def Language.IsRegular (L : Language T) : Prop :=
  ∃ g : RLG T, g.language = L

/-- Regular languages are context-free. -/
theorem IsRegular_implies_IsCF {L : Language T} :
    L.IsRegular → L.IsCF :=
by
  rintro ⟨g, hg⟩
  use g.toCFG
  exact hg
