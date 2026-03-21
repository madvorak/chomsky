import Chomsky.Classes.ContextSensitive.Basics.Toolbox

namespace ContextSensitiveDemo

inductive Te | a | b | c
inductive Nt | B | C | R | S | X | Y | Z

open Te Nt

private def sa : Symbol Te Nt := Symbol.terminal a
private def sb : Symbol Te Nt := Symbol.terminal b
private def sc : Symbol Te Nt := Symbol.terminal c
private def B : Symbol Te Nt := Symbol.nonterminal Nt.B
private def C : Symbol Te Nt := Symbol.nonterminal Nt.C
private def R : Symbol Te Nt := Symbol.nonterminal Nt.R
private def S : Symbol Te Nt := Symbol.nonterminal Nt.S
private def X : Symbol Te Nt := Symbol.nonterminal Nt.X
private def Y : Symbol Te Nt := Symbol.nonterminal Nt.Y
private def Z : Symbol Te Nt := Symbol.nonterminal Nt.Z

/-- rule `S → aSBC | aRC` as two context-sensitive rules -/
private def r1 : CSRule Te Nt := ⟨[], Nt.S, [], [sa, S, B, C]⟩
private def r2 : CSRule Te Nt := ⟨[], Nt.S, [], [sa, R, C]⟩

/-- non-contracting rule `CB → BC` modelled by `CB → XB → XC → BC` -/
private def r3  : CSRule Te Nt := ⟨[], Nt.C, [B], [X]⟩
private def r3a : CSRule Te Nt := ⟨[X], Nt.B, [], [C]⟩
private def r3b : CSRule Te Nt := ⟨[], Nt.X, [C], [B]⟩

/-- non-contracting rule `RB → bR` modelled by `RB → YB → YR → bR` -/
private def r4  : CSRule Te Nt := ⟨[], Nt.R, [B], [Y]⟩
private def r4a : CSRule Te Nt := ⟨[Y], Nt.B, [], [R]⟩
private def r4b : CSRule Te Nt := ⟨[], Nt.Y, [R], [sb]⟩

/-- non-contracting rule `RC → bc` modelled by `RC → ZC → Zc → bc` -/
private def r5  : CSRule Te Nt := ⟨[], Nt.R, [C], [Z]⟩
private def r5a : CSRule Te Nt := ⟨[Z], Nt.C, [], [sc]⟩
private def r5b : CSRule Te Nt := ⟨[], Nt.Z, [sc], [sb]⟩

/-- context-sensitive rule `cC → cc` -/
private def r6 : CSRule Te Nt := ⟨[sc], Nt.C, [], [sc]⟩

def myGrammar : CSG Te where
  nt := Nt
  initial := Nt.S
  rules := [r1, r2, r3, r3a, r3b, r4, r4a, r4b, r5, r5a, r5b, r6]

end ContextSensitiveDemo
