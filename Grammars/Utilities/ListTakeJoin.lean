/- Written by Patrick Johnson and released into the public domain at:
  https://github.com/user7230724/lean-projects/blob/master/src/list_take_join/main.lean
! This file was ported from Lean 3 source module utilities.written_by_others.list_take_join
-/
import Mathlib

namespace List

variable {α : Type _}

/-private noncomputable def get_max [Inhabited α] [LinearOrder α] (P : α → Prop) :=
  Classical.epsilon fun x : α => P x ∧ ∀ y : α, x < y → ¬P y

private theorem epsilon_eq [Inhabited α] {P : α → Prop} {x : α} (h₁ : P x)
    (h₂ : ∀ y : α, P y → y = x) : Classical.epsilon P = x :=
  by
  have h₃ : P = fun y : α => y = x := by
    ext y; constructor <;> intro h₃
    · exact h₂ y h₃
    · rwa [h₃]
  subst h₃; apply Classical.epsilon_singleton

private theorem nat_get_max_spec {P : ℕ → Prop} (h₁ : ∃ x : ℕ, P x)
    (h₂ : ∃ x : ℕ, ∀ y : ℕ, x ≤ y → ¬P y) : P (getMax P) ∧ ∀ x : ℕ, getMax P < x → ¬P x :=
  by
  cases' h₁ with m h₁; cases' h₂ with n h₂; induction' n with n ih
  · cases h₂ m (zero_le m) h₁
  · simp_rw [Nat.succ_le_iff] at h₂ ; by_cases h₃ : P n
    · have : get_max P = n := by
        rw [get_max]; apply epsilon_eq
        · use h₃; rintro k hk; exact h₂ k hk
        · rintro k ⟨h₄, h₅⟩; by_contra h₆
          rw [← Ne, ne_iff_lt_or_gt] at h₆ ; cases h₆
          · cases h₅ n h₆ h₃; · cases h₂ k h₆ h₄
      rw [this] at *; clear this; exact ⟨h₃, h₂⟩
    · apply ih; rintro k hk; rw [le_iff_eq_or_lt] at hk ; rcases hk with (rfl | hk)
      · exact h₃
      · exact h₂ k hk -/

theorem take_join_of_lt {L : List (List α)} {n : ℕ} (notall : n < L.join.length) :
    ∃ m k : ℕ,
      ∃ mlt : m < L.length,
        k < (L.nthLe m mlt).length ∧ L.join.take n = (L.take m).join ++ (L.nthLe m mlt).take k :=
  by sorry /-
  generalize hX : L.length = X; symm at hX 
  generalize hN : L.join.length = N; symm at hN 
  rw [← hN] at notall ; have hl : L ≠ [] := by rintro rfl; rw [hN] at notall ; cases notall
  generalize hP : fun m : ℕ => (L.take m).join.length ≤ n = P; symm at hP 
  generalize hm : get_max P = m; symm at hm 
  generalize hk : n - (L.take m).join.length = k; symm at hk 
  have hP0 : P 0 := by rw [hP]; simp
  have hPX : ∀ r : ℕ, X ≤ r → ¬P r := by
    rintro r hr; rw [hP]; push_neg; convert notall; rw [hX] at hr 
    rw [hN, List.take_all_of_le hr]
  obtain ⟨hm₁, hm₂⟩ := nat_get_max_spec ⟨0, hP0⟩ ⟨X, hPX⟩; rw [← hm] at hm₁ hm₂ 
  have hm₃ : ¬P m.succ := hm₂ _ (Nat.lt_succ_self m)
  refine' ⟨m, k, _, _, _⟩
  · rw [← hX]; by_contra' hx; cases hPX m hx hm₁
  · generalize_proofs h₁; rw [hP] at hm₁ hm₃ ; push_neg at hm₃ 
    by_contra' hk₁; obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk₁
    replace hk := congr_arg (fun x : ℕ => x + (L.take m).join.length) hk
    dsimp at hk ; rw [Nat.sub_add_cancel hm₁] at hk ; rw [← hk] at hm₃ 
    contrapose! hm₃; rw [add_comm, ← add_assoc]; convert le_self_add
    simp [Nat.succ_eq_add_one, List.take_add, List.join_append, List.length_append]
    rw [List.take_one_drop_eq_of_lt_length', map_singleton, sum_singleton]
  conv =>
    lhs
    rw [← List.take_append_drop m.succ L, List.join_append]
  have hn₁ : (L.take m).join.length ≤ n := by rwa [hP] at hm₁ 
  have hn₂ : n < (L.take m.succ).join.length := by rw [hP] at hm₃ ; push_neg at hm₃ ; exact hm₃
  rw [List.take_append_of_le_length (le_of_lt hn₂)]
  change m.succ with m + 1; have hmX : m < X := by by_contra' hx; exact hPX m hx hm₁
  rw [List.take_add, List.join_append, List.take_one_drop_eq_of_lt_length', List.join, List.join,
    List.append_nil]
  swap; · rwa [← hX]
  have : n = (List.take m L).join.length + k := by rw [hk]; exact (Nat.add_sub_of_le hn₁).symm
  subst this; rw [List.take_append] -/

end List

