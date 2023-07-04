import Grammars.Classes.Unrestricted.Basics.Definition

/-- Transformation rule for a grammar in the Kuroda normal form. -/
inductive KurodaRule (T : Type) (N : Type)
  | two_two (A B C D : N) : KurodaRule T N
  | one_two (A B C : N) : KurodaRule T N
  | one_one (A : N) (t : T) : KurodaRule T N
  | one_nil (A : N) : KurodaRule T N

/-- Grammar in the Kuroda normal form that generates words
    over the alphabet `T` (a type of terminals). -/
structure KurodaGrammar (T : Type) where
  nt : Type
  initial : nt
  rules : List (KurodaRule T nt)

def grule_of_kurodaRule {T : Type} {N : Type} : KurodaRule T N → Grule T N
  | KurodaRule.two_two A B C D =>
      Grule.mk [] A [Symbol.nonterminal B] [Symbol.nonterminal C, Symbol.nonterminal D]
  | KurodaRule.one_two A B C => Grule.mk [] A [] [Symbol.nonterminal B, Symbol.nonterminal C]
  | KurodaRule.one_one A t => Grule.mk [] A [] [Symbol.terminal t]
  | KurodaRule.one_nil A => Grule.mk [] A [] []

def grammar_of_kurodaGrammar {T : Type} (k : KurodaGrammar T) : Grammar T :=
  Grammar.mk k.nt k.initial (List.map grule_of_kurodaRule k.rules)

theorem kurodaGrammar_always_exists {T : Type} (L : Language T) :
  IsRE L → ∃ k : KurodaGrammar T, Grammar.Language (grammar_of_kurodaGrammar k) = L :=
sorry
