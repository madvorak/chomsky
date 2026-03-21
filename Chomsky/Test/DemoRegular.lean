import Chomsky.Classes.Regular.Basics.Definition

namespace RegularDemo

inductive Alphabet | a | b
inductive Nonterminal | S | A

open Alphabet Nonterminal

/-- Regular grammar for { a^n b | n ≥ 0 } -/
private def r1 : RLRule Alphabet Nonterminal := RLRule.nonterminal S a S
private def r2 : RLRule Alphabet Nonterminal := RLRule.terminal S b

def regularGrammar : RLG Alphabet where
  nt := Nonterminal
  initial := S
  rules := [r1, r2]

end RegularDemo
