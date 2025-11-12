import Chomsky.Classes.ContextFree.Basics.Toolbox
import Chomsky.Utilities.LanguageOperations
import Chomsky.Utilities.ListUtils

variable {T : Type}

private def CFG.reverse (g : CFG T) : CFG T :=
  CFG.mk
    g.nt
    g.initial
    (List.map (fun r : g.nt × List (Symbol T g.nt) => (r.fst, List.reverse r.snd)) g.rules)

private lemma dual_of_reversalGrammar (g : CFG T) :
  g.reverse.reverse = g :=
by
  cases' g with g_nt g_initial g_rules
  simp only [CFG.reverse, List.map_map, CFG.mk.injEq, heq_eq_eq, true_and]
  convert_to
    List.map (fun r : g_nt × List (Symbol T g_nt) => (r.fst, r.snd.reverse.reverse)) g_rules =
    g_rules
  simp [List.reverse_reverse]

private lemma derives_reversed (g : CFG T) (v : List (Symbol T g.nt)) :
  g.reverse.Derives [Symbol.nonterminal g.reverse.initial] v →
    g.Derives [Symbol.nonterminal g.initial] v.reverse :=
by
  intro hv
  induction' hv with u w _ orig ih
  · rw [List.reverse_singleton]
    apply cf_deri_self
  apply cf_deri_of_deri_tran ih
  rcases orig with ⟨r, rin, x, y, bef, aft⟩
  change r ∈ List.map (fun r : g.nt × List (Symbol T g.nt) => (r.fst, List.reverse r.snd)) g.rules at rin
  rw [List.mem_map] at rin
  rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
  use r₀
  constructor
  · exact rin₀
  use y.reverse
  use x.reverse
  constructor
  · rw [←List.reverse_singleton, ←List.reverse_append_append]
    have fst_from_r : r₀.fst = r.fst
    · rw [←r_from_r₀]
    rw [fst_from_r]
    exact congr_arg List.reverse bef
  · have snd_from_r : r₀.snd = r.snd.reverse
    · rw [←r_from_r₀, List.reverse_reverse]
    rw [snd_from_r, ←List.reverse_append_append]
    exact congr_arg List.reverse aft

private lemma reversed_word_in_original_language {g : CFG T} {w : List T}
    (hgw : w ∈ g.reverse.language) :
  w.reverse ∈ g.language :=
by
  unfold CFG.language at *
  rw [Set.mem_setOf_eq] at *
  rw [List.map_reverse]
  exact derives_reversed g (List.map Symbol.terminal w) hgw

/-- The class of context-free languages is closed under reversal. -/
theorem CF_of_reverse_CF (L : Language T) :
  L.IsCF → L.reverse.IsCF :=
by
  rintro ⟨g, hgL⟩
  rw [←hgL]
  use g.reverse
  apply Set.eq_of_subset_of_subset
  · intro _
    exact reversed_word_in_original_language
  · intro w hwL
    have pre_reversal : ∃ g₀ : CFG T, g = g₀.reverse
    · use g.reverse
      rw [dual_of_reversalGrammar]
    cases' pre_reversal with g₀ pre_rev
    rw [pre_rev] at hwL ⊢
    have finished_modulo_reverses := reversed_word_in_original_language hwL
    rw [dual_of_reversalGrammar]
    rw [List.reverse_reverse] at finished_modulo_reverses
    exact finished_modulo_reverses
