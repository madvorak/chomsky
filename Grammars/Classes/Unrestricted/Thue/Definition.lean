import Mathlib.Logic.Relation
import Mathlib.Computability.Language


inductive Symbol (T : Type) (N : Type) -- duplicate definition
  | terminal    (t : T) : Symbol T N -- or rather "letters"
  | nonterminal (n : N) : Symbol T N -- or rather "markers"

structure Trule (T : Type) (N : Type) where
  inputL : List T
  inputN : N
  inputR : List (Symbol T N) -- probably change to monolitic input side
  output : List (Symbol T N)

structure System (T : Type) where
  nt : Type                 -- type of nonterminals / markers
  special : nt              -- special marker to be prepended
  rules : List (Trule T nt) -- rewrite rules

variable {T : Type}


def System.Transforms (h : System T) (w₁ w₂ : List (Symbol T h.nt)) : Prop :=
  ∃ r : Trule T h.nt,
    r ∈ h.rules ∧
    ∃ u v : List (Symbol T h.nt),
      w₁ = u ++ (List.map Symbol.terminal r.inputL) ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v ∧
      w₂ = u ++ r.output ++ v

def System.Derives (h : System T) : List (Symbol T h.nt) → List (Symbol T h.nt) → Prop :=
  Relation.ReflTransGen h.Transforms -- probably add counting steps

def System.Language (h : System T) : Language T :=
  setOf (fun w => h.Derives (Symbol.nonterminal h.special :: List.map Symbol.terminal w) [])
-- probably extract `(Symbol.nonterminal h.special :: List.map Symbol.terminal w)` to `h.initiate w`

def IsTre (L : Language T) : Prop :=
  ∃ h : System T, h.Language = L

/-- Is there always at most one transformation possible? -/
def System.IsDeterministic (h : System T) : Prop :=
  ∀ w : List T, ∀ s : List (Symbol T h.nt),
    h.Derives (Symbol.nonterminal h.special :: List.map Symbol.terminal w) s →
      ∀ x y : List (Symbol T h.nt), h.Transforms s x ∧ h.Transforms s y → x = y

def IsDet (L : Language T) : Prop :=
  ∃ h : System T, h.Language = L ∧ h.IsDeterministic
