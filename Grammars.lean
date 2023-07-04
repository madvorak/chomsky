import Mathlib.Data.List.TFAE

lemma TFAE_congr {α : Type} (P : List (α → Prop))
    (ass : ∀ a : α, (P.map (fun p => p a)).TFAE) :
  (P.map (fun p => ∀ a, p a)).TFAE :=
by
  intros p₁ hp₁ p₂ hp₂
  rw [List.mem_map] at hp₁ hp₂
  rcases hp₁ with ⟨x, xin, hx⟩
  rcases hp₂ with ⟨y, yin, hy⟩
  rw [← hx, ← hy]
  constructor <;> intros hyp a <;> specialize ass a (x a) _ (y a) _
  any_goals rw [List.mem_map]
  repeat
    · exact ⟨x, xin, rfl⟩
    · exact ⟨y, yin, rfl⟩
    · tauto
