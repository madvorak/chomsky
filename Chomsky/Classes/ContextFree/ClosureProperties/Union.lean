import Chomsky.Classes.ContextFree.Basics.Inclusion
import Chomsky.Classes.Unrestricted.ClosureProperties.Union

variable {T : Type}

private def liftCFR₁ {N₁ : Type} (N₂ : Type) (r : N₁ × List (Symbol T N₁)) :
  Option (N₁ ⊕ N₂) × List (Symbol T (Option (N₁ ⊕ N₂))) :=
⟨some ◩r.fst, liftString (Option.some ∘ Sum.inl) r.snd⟩

private def liftCFR₂ (N₁ : Type) {N₂ : Type} (r : N₂ × List (Symbol T N₂)) :
  Option (N₁ ⊕ N₂) × List (Symbol T (Option (N₁ ⊕ N₂))) :=
⟨some ◪r.fst, liftString (Option.some ∘ Sum.inr) r.snd⟩

private def unionCFG (g₁ g₂ : CFG T) : CFG T :=
  CFG.mk (Option (g₁.nt ⊕ g₂.nt)) none (
    (none, [Symbol.nonterminal (some ◩g₁.initial)]) :: (
    (none, [Symbol.nonterminal (some ◪g₂.initial)]) :: (
    g₁.rules.map (liftCFR₁ g₂.nt) ++
    g₂.rules.map (liftCFR₂ g₁.nt))))

private lemma unionCFG_language_eq_unionGrammar_language (g₁ g₂ : CFG T) :
  (unionCFG g₁ g₂).language = (unionGrammar g₁.toGeneral g₂.toGeneral).language :=
by
  rw [CFG.language_eq_toGeneral_language]
  simp only [unionCFG, unionGrammar, CFG.toGeneral, List.cons_append, List.map_cons, List.map_append, List.map_map]
  rfl

theorem CF_of_CF_u_CF (L₁ : Language T) (L₂ : Language T) :
  L₁.IsCF ∧ L₂.IsCF → (L₁ + L₂).IsCF :=
by
  intro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  rw [g₁.language_eq_toGeneral_language] at eq_L₁
  rw [g₂.language_eq_toGeneral_language] at eq_L₂
  use unionCFG g₁ g₂
  rw [unionCFG_language_eq_unionGrammar_language]
  apply Set.eq_of_subset_of_subset
  · intro w hw
    rw [←eq_L₁, ←eq_L₂]
    exact in_L₁_or_L₂_of_in_union hw
  · intro w hw
    exact hw.casesOn (in_union_of_in_L₁ <| eq_L₁ ▸ ·) (in_union_of_in_L₂ <| eq_L₂ ▸ ·)

#print axioms CF_of_CF_u_CF
