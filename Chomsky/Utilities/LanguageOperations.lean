import Mathlib.Computability.Language

variable {T : Type}

def reverseLang (L : Language T) : Language T := fun w : List T => w.reverse ∈ L

def bijemapLang {T' : Type} (L : Language T) (π : Equiv T T') : Language T' := fun w : List T' =>
  List.map π.invFun w ∈ L

def permuteLang (L : Language T) (π : Equiv.Perm T) : Language T :=
  bijemapLang L π
