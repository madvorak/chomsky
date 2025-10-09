import Chomsky.Classes.ContextFree.Basics.Inclusion
import Chomsky.Classes.Unrestricted.ClosureProperties.Union

variable {T : Type}


private def liftCFrule₁ {N₁ : Type} (N₂ : Type) (r : N₁ × List (Symbol T N₁)) :
  Option (Sum N₁ N₂) × List (Symbol T (Option (Sum N₁ N₂))) :=
(some ◩r.fst, liftString (Option.some ∘ Sum.inl) r.snd)

private def liftCFrule₂ (N₁ : Type) {N₂ : Type} (r : N₂ × List (Symbol T N₂)) :
  Option (Sum N₁ N₂) × List (Symbol T (Option (Sum N₁ N₂))) :=
(some ◪r.fst, liftString (Option.some ∘ Sum.inr) r.snd)

private def unionCFG (g₁ g₂ : CFG T) : CFG T :=
  CFG.mk (Option (Sum g₁.nt g₂.nt)) none (
    (none, [Symbol.nonterminal (some ◩g₁.initial)]) ::
    (none, [Symbol.nonterminal (some ◪g₂.initial)]) ::
    List.map (liftCFrule₁ g₂.nt) g₁.rules ++
    List.map (liftCFrule₂ g₁.nt) g₂.rules)

private lemma unionCFG_same_language (g₁ g₂ : CFG T) :
  (unionCFG g₁ g₂).language =
  (unionGrammar (grammar_of_cfg g₁) (grammar_of_cfg g₂)).language :=
by
  rw [cfLanguage_eq_grammarLanguage]
  unfold unionCFG grammar_of_cfg unionGrammar
  dsimp only [List.map]
  repeat' rw [List.map_append]
  simp
  sorry

private theorem bonus_CF_of_CF_u_CF (L₁ : Language T) (L₂ : Language T) :
  L₁.IsCF ∧ L₂.IsCF → (L₁ + L₂).IsCF :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  rw [cfLanguage_eq_grammarLanguage g₁] at eq_L₁
  rw [cfLanguage_eq_grammarLanguage g₂] at eq_L₂
  use unionCFG g₁ g₂
  rw [unionCFG_same_language]
  apply Set.eq_of_subset_of_subset
  · intro w hyp
    rw [← eq_L₁, ← eq_L₂]
    exact in_L₁_or_L₂_of_in_union hyp
  · intro w hyp
    cases' hyp with case_1 case_2
    · rw [← eq_L₁] at case_1
      exact in_union_of_in_L₁ case_1
    · rw [← eq_L₂] at case_2
      exact in_union_of_in_L₂ case_2
