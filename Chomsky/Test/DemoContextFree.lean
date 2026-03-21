import Chomsky.Classes.ContextFree.Basics.Toolbox

namespace ContextFreeDemo

private def a_ : Fin 3 := 0
private def a : Symbol (Fin 3) (Fin 2) := Symbol.terminal a_
private def b_ : Fin 3 := 1
private def b : Symbol (Fin 3) (Fin 2) := Symbol.terminal b_
private def c_ : Fin 3 := 2
private def c : Symbol (Fin 3) (Fin 2) := Symbol.terminal c_

private def S_ : Fin 2 := 0
private def S : Symbol (Fin 3) (Fin 2) := Symbol.nonterminal S_
private def R_ : Fin 2 := 1
private def R : Symbol (Fin 3) (Fin 2) := Symbol.nonterminal R_

def grAdd : CFG (Fin 3) where
  nt := Fin 2
  initial := S_
  rules := [
    (S_, [a, S, c]),
    (S_, [R]),
    (R_, [b, R, c]),
    (R_, [])
  ]

end ContextFreeDemo
