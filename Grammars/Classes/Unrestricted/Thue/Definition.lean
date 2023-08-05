import Mathlib.Computability.Language


inductive Tsymb (α : Type) (β : Type)
  | letter (a : α) : Tsymb α β
  | marker (b : β) : Tsymb α β

structure Trule (α : Type) (β : Type) where
  input : List (Tsymb α β)
  ouput : List (Tsymb α β)

structure Tsys (α : Type) where -- alphabet
  beta : Type                   -- markers
  special : beta                -- to be prepended
  ruleset : List (Trule α beta) -- rewrite rules

variable {α : Type}

def Tsys.initiate (h : Tsys α) (w : List α) : List (Tsymb α h.beta) :=
  Tsymb.marker h.special :: List.map Tsymb.letter w


def Tsys.Transforms (h : Tsys α) (w₁ w₂ : List (Tsymb α h.beta)) : Prop :=
  ∃ r : Trule α h.beta,
    r ∈ h.ruleset ∧
    ∃ u v : List (Tsymb α h.beta), w₁ = u ++ r.input ++ v ∧ w₂ = u ++ r.ouput ++ v

inductive Tsys.Derives (h : Tsys α) : List (Tsymb α h.beta) → List (Tsymb α h.beta) → ℕ → Prop
  | refl (w : List (Tsymb α h.beta)) : h.Derives w w 0
  | tail (u v w : List (Tsymb α h.beta)) (n : ℕ) : h.Derives u v n → h.Transforms v w → h.Derives u w n.succ

def Tsys.language (h : Tsys α) : Language α :=
  setOf (fun w => ∃ n : ℕ, h.Derives (h.initiate w) [] n)

def IsThue (L : Language α) : Prop :=
  ∃ h : Tsys α, h.language = L

def Tsys.IsDeterministic (h : Tsys α) : Prop :=
  ∀ w : List α, ∀ s : List (Tsymb α h.beta), ∀ n : ℕ, h.Derives (h.initiate w) s n →
    ∀ x y : List (Tsymb α h.beta), h.Transforms s x ∧ h.Transforms s y → x = y

def IsDethue (L : Language α) : Prop :=
  ∃ h : Tsys α, h.language = L ∧ h.IsDeterministic

def Tsys.IsDtime (h : Tsys α) (f : ℕ → ℕ) : Prop :=
  h.IsDeterministic ∧
  ∃ c : ℕ, ∀ w : List α, ∀ s : List (Tsymb α h.beta), ∀ n : ℕ,
    h.Derives (h.initiate w) s n → n ≤ c * f w.length
