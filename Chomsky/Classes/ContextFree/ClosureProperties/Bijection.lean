/-import Project.Classes.ContextFree.Basics.Toolbox
import Project.Utilities.LanguageOperations

variable {T₁ T₂ N : Type}

private def sT₂_of_sT₁ (π : Equiv T₁ T₂) : Symbol T₁ N → Symbol T₂ N
  | Symbol.terminal t => Symbol.terminal (π.toFun t)
  | Symbol.nonterminal n => Symbol.nonterminal n

private def sT₁_of_sT₂ (π : Equiv T₁ T₂) : Symbol T₂ N → Symbol T₁ N
  | Symbol.terminal t => Symbol.terminal (π.invFun t)
  | Symbol.nonterminal n => Symbol.nonterminal n

private def lsT₂_of_lsT₁ (π : Equiv T₁ T₂) : List (Symbol T₁ N) → List (Symbol T₂ N) :=
  List.map (sT₂OfST₁ π)

private def lsT₁_of_lsT₂ (π : Equiv T₁ T₂) : List (Symbol T₂ N) → List (Symbol T₁ N) :=
  List.map (sT₁OfST₂ π)

/-- The class of context-free languages is closed under bijection between terminal alphabets. -/
lemma CF_of_bijemap_CF (π : Equiv T₁ T₂) (L : Language T₁) : L.IsCF → (L.bijemap π).IsCF :=
  by
  rintro ⟨g, hg⟩
  let g' : CFG T₂ :=
    CFG.mk g.nt g.initial
      (List.map (fun r : g.nt × List (Symbol T₁ g.nt) => (r.fst, lsT₂_of_lsT₁ π r.snd)) g.rules)
  use g'
  apply Set.eq_of_subset_of_subset
  · intro w hw
    unfold bijemapLang
    change List.map π.inv_fun w ∈ L
    rw [← hg]
    unfold cFLanguage at hw ⊢
    rw [Set.mem_setOf_eq] at hw ⊢
    unfold CFGenerates at hw ⊢
    unfold CFGeneratesStr at hw ⊢
    have deri_of_deri :
      ∀ v : List (Symbol T₂ g'.nt),
        CFDerives g' [Symbol.nonterminal g'.initial] v →
          CFDerives g [Symbol.nonterminal g.initial] (lsT₁_of_lsT₂ π v) :=
      by
      intro v hv
      induction' hv with u v trash orig ih
      · apply CF_deri_self
      apply CF_deri_of_deri_tran
      · exact ih
      rcases orig with ⟨r, r_in, x, y, bef, aft⟩
      let r₁ := (r.fst, lsT₁_of_lsT₂ π r.snd)
      let x₁ := lsT₁_of_lsT₂ π x
      let y₁ := lsT₁_of_lsT₂ π y
      use r₁
      constructor
      · change (r.fst, lsT₁_of_lsT₂ π r.snd) ∈ g.rules
        rw [List.mem_map, Prod.exists] at r_in
        rcases r_in with ⟨a, b, ab_in, ab_eq⟩
        have a_eq : a = r.fst := (congr_arg Prod.fst ab_eq).congr_right.mp rfl
        have b_eq : lsT₂_of_lsT₁ π b = r.snd := (congr_arg Prod.snd ab_eq).congr_right.mp rfl
        rw [a_eq] at ab_in
        convert ab_in
        rw [← b_eq]
        unfold lsT₁_of_lsT₂
        unfold lsT₂_of_lsT₁
        rw [List.map_map]
        ext1
        rw [List.get?_map]
        cases b.nth n
        ·-- none = none
          rfl
        cases val; swap
        ·-- nonterminal = nonterminal
          rfl
        ·-- (sT₁_of_sT₂ π ∘ sT₂_of_sT₁ π) terminal = terminal
          simp [sT₂_of_sT₁, sT₁_of_sT₂, Equiv.left_inv]
      use x₁
      use y₁
      constructor
      · rw [bef]
        unfold lsT₁_of_lsT₂
        rw [List.map_append]
        rw [List.map_append]
        rfl
      · rw [aft]
        unfold lsT₁_of_lsT₂
        rw [List.map_append]
        rw [List.map_append]
        rfl
    specialize deri_of_deri (List.map Symbol.terminal w) hw
    unfold lsT₁_of_lsT₂ at deri_of_deri
    rw [List.map_map] at *
    convert deri_of_deri
  · intro w hw
    unfold bijemapLang at hw
    change List.map π.inv_fun w ∈ L at hw
    rw [← hg] at hw
    unfold cFLanguage at hw
    rw [Set.mem_setOf_eq] at hw
    unfold CFGenerates at hw
    rw [List.map_map] at hw
    unfold CFGeneratesStr at hw
    unfold cFLanguage
    change CFGeneratesStr g' (List.map Symbol.terminal w)
    unfold CFGeneratesStr
    have deri_of_deri :
      ∀ v : List (Symbol T₁ g.nt),
        CFDerives g [Symbol.nonterminal g.initial] v →
          CFDerives g' [Symbol.nonterminal g'.initial] (lsT₂_of_lsT₁ π v) :=
      by
      intro v hv
      induction' hv with u v trash orig ih
      · apply CF_deri_self
      apply CF_deri_of_deri_tran
      · exact ih
      rcases orig with ⟨r, r_in, x, y, bef, aft⟩
      let r₂ := (r.fst, lsT₂_of_lsT₁ π r.snd)
      let x₂ := lsT₂_of_lsT₁ π x
      let y₂ := lsT₂_of_lsT₁ π y
      use r₂
      constructor
      · rw [List.mem_map, Prod.exists]
        use r.fst
        use r.snd
        constructor
        · convert r_in
          exact Prod.ext rfl rfl
        constructor <;> rfl
      use x₂
      use y₂
      constructor
      · rw [bef]
        unfold lsT₂_of_lsT₁
        rw [List.map_append]
        rw [List.map_append]
        rfl
      · rw [aft]
        unfold lsT₂_of_lsT₁
        rw [List.map_append]
        rw [List.map_append]
        rfl
    specialize deri_of_deri (List.map (Symbol.terminal ∘ π.inv_fun) w) hw
    rw [lsT₂_of_lsT₁] at deri_of_deri
    rw [List.map_map] at deri_of_deri
    convert deri_of_deri
    ext1
    change Symbol.terminal x = sT₂_of_sT₁ π (Symbol.terminal (π.inv_fun x))
    unfold sT₂_of_sT₁
    rw [Equiv.right_inv]
-/
