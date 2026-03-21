import Chomsky.Classes.Unrestricted.Basics.Toolbox

inductive Alphabet
  | _a | _b | _c

inductive Inner
  | _S | _L | _R | _X | _B | _M | _E | _C | _K

namespace UnrestrictedDemo

open Alphabet Inner

private def a_ := _a
private def b_ := _b
private def c_ := _c

private def S_ := _S
private def L_ := _L
private def R_ := _R
private def X_ := _X
private def B_ := _B
private def M_ := _M
private def E_ := _E
private def C_ := _C
private def K_ := _K

private abbrev MyChar := Symbol Alphabet Inner

private def a : MyChar := Symbol.terminal a_
private def b : MyChar := Symbol.terminal b_
private def c : MyChar := Symbol.terminal c_
private def S : MyChar := Symbol.nonterminal S_
private def L : MyChar := Symbol.nonterminal L_
private def R : MyChar := Symbol.nonterminal R_
private def X : MyChar := Symbol.nonterminal X_
private def B : MyChar := Symbol.nonterminal B_
private def M : MyChar := Symbol.nonterminal M_
private def E : MyChar := Symbol.nonterminal E_
private def C : MyChar := Symbol.nonterminal C_
private def K : MyChar := Symbol.nonterminal K_

/-
Grammar for unary multiplication
{ a^m . b^n . c^(m*n) | m n ∈ ℕ }
-/

private def S_LR   : Grule Alphabet Inner := ⟨[], S_, [], [L, R]⟩
private def L_aLX  : Grule Alphabet Inner := ⟨[], L_, [], [a, L, X]⟩
private def R_BR   : Grule Alphabet Inner := ⟨[], R_, [], [B, R]⟩
private def L_M    : Grule Alphabet Inner := ⟨[], L_, [], [M]⟩
private def R_E    : Grule Alphabet Inner := ⟨[], R_, [], [E]⟩
private def XB_BCX : Grule Alphabet Inner := ⟨[X], B_, [], [B, C, X]⟩
private def CB_BC  : Grule Alphabet Inner := ⟨[C], B_, [], [B, C]⟩
private def XC_CX  : Grule Alphabet Inner := ⟨[X], C_, [], [C, X]⟩
private def XE_E   : Grule Alphabet Inner := ⟨[X], E_, [], [E]⟩
private def MB_bM  : Grule Alphabet Inner := ⟨[M], B_, [], [b, M]⟩
private def M_K    : Grule Alphabet Inner := ⟨[], M_, [], [K]⟩
private def KC_cK  : Grule Alphabet Inner := ⟨[K], C_, [], [c, K]⟩
private def KE_nil : Grule Alphabet Inner := ⟨[K], E_, [], []⟩

def grMul : Grammar Alphabet where
  nt := Inner
  initial := S_
  rules := [S_LR, L_aLX, R_BR, L_M, R_E, XB_BCX, CB_BC, XC_CX, XE_E, MB_bM, M_K, KC_cK, KE_nil]

end UnrestrictedDemo
