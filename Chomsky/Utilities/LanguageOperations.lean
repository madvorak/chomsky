import Mathlib.Computability.Language

variable {T : Type}

def Language.bijemap {T' : Type} (L : Language T) (π : Equiv T T') : Language T' :=
  fun w : List T' => w.map π.invFun ∈ L

def Language.permute (L : Language T) (π : Equiv.Perm T) : Language T :=
  L.bijemap π
