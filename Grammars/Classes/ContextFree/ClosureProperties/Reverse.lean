/-import Project.Classes.ContextFree.Basics.Toolbox
import Project.Utilities.LanguageOperations
import Project.Utilities.ListUtils

variable {T : Type}

section Auxiliary

private def reversal_grammar (g : CFGrammar T) : CFGrammar T :=
  CFGrammar.mk g.Nt g.initial
    (List.map (fun r : g.Nt × List (Symbol T g.Nt) => (r.fst, List.reverse r.snd)) g.rules)

private lemma dual_of_reversal_grammar (g : CFGrammar T) :
    reversalGrammar (reversalGrammar g) = g :=
  by
  cases g
  unfold reversal_grammar
  dsimp only
  rw [List.map_map]
  simp only [eq_self_iff_true, heq_iff_eq, true_and_iff]
  change
    List.map
        ((fun r : g_nt × List (Symbol T g_nt) => (r.fst, r.snd.reverse)) ∘
          fun r : g_nt × List (Symbol T g_nt) => (r.fst, r.snd.reverse))
        g_rules =
      g_rules
  convert_to
    List.map (fun r : g_nt × List (Symbol T g_nt) => (r.fst, r.snd.reverse.reverse)) g_rules =
      g_rules
  convert_to List.map (fun r : g_nt × List (Symbol T g_nt) => (r.fst, r.snd)) g_rules = g_rules
  · simp [List.reverse_reverse]
  · simp

private lemma derives_reversed (g : CFGrammar T) (v : List (Symbol T g.Nt)) :
    CFDerives (reversalGrammar g) [Symbol.nonterminal (reversalGrammar g).initial] v →
      CFDerives g [Symbol.nonterminal g.initial] v.reverse :=
  by
  intro hv
  induction' hv with u w trash orig ih
  · rw [List.reverse_singleton]
    apply CF_deri_self
  apply CF_deri_of_deri_tran ih
  rcases orig with ⟨r, rin, x, y, bef, aft⟩
  change
    r ∈ List.map (fun r : g.nt × List (Symbol T g.nt) => (r.fst, List.reverse r.snd)) g.rules at rin
  rw [List.mem_map] at rin
  rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
  use r₀
  constructor
  · exact rin₀
  use y.reverse
  use x.reverse
  constructor
  · rw [← List.reverse_singleton]
    rw [← List.reverse_append_append]
    have fst_from_r : r₀.fst = r.fst := by rw [← r_from_r₀]
    rw [fst_from_r]
    exact congr_arg List.reverse bef
  · have snd_from_r : r₀.snd = r.snd.reverse :=
      by
      rw [← r_from_r₀]
      rw [List.reverse_reverse]
    rw [snd_from_r]
    rw [← List.reverse_append_append]
    exact congr_arg List.reverse aft

private lemma reversed_word_in_original_language {g : CFGrammar T} {w : List T}
    (hyp : w ∈ cFLanguage (reversalGrammar g)) : w.reverse ∈ cFLanguage g :=
  by
  unfold cFLanguage at *
  rw [Set.mem_setOf_eq] at *
  unfold CFGenerates at *
  unfold CFGeneratesStr at *
  rw [List.map_reverse]
  exact derives_reversed g (List.map Symbol.terminal w) hyp

end Auxiliary

/-- The class of context-free languages is closed under reversal. -/
lemma CF_of_reverse_CF (L : Language T) : IsCF L → IsCF (reverseLang L) :=
  by
  rintro ⟨g, hgL⟩
  rw [← hgL]
  use reversal_grammar g
  unfold reverseLang
  apply Set.eq_of_subset_of_subset
  · intro w hwL
    change w.reverse ∈ cFLanguage g
    exact reversed_word_in_original_language hwL
  · intro w hwL
    change w.reverse ∈ cFLanguage g at hwL
    have pre_reversal : ∃ g₀, g = reversal_grammar g₀ :=
      by
      use reversal_grammar g
      rw [dual_of_reversal_grammar]
    cases' pre_reversal with g₀ pre_rev
    rw [pre_rev] at hwL ⊢
    have finished_modulo_reverses := reversed_word_in_original_language hwL
    rw [dual_of_reversal_grammar]
    rw [List.reverse_reverse] at finished_modulo_reverses
    exact finished_modulo_reverses
-/
