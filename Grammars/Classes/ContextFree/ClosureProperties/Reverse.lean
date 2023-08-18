import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.LanguageOperations
import Grammars.Utilities.ListUtils

variable {T : Type}

private def reversalGrammar (g : CFgrammar T) : CFgrammar T :=
  CFgrammar.mk
    g.nt
    g.initial
    (List.map (fun r : g.nt × List (Symbol T g.nt) => (r.fst, List.reverse r.snd)) g.rules)

private lemma dual_of_reversalGrammar (g : CFgrammar T) :
  reversalGrammar (reversalGrammar g) = g :=
by
  cases' g with g_nt g_initial g_rules
  simp only [reversalGrammar, List.map_map, CFgrammar.mk.injEq, heq_eq_eq, true_and]
  convert_to
    List.map (fun r : g_nt × List (Symbol T g_nt) => (r.fst, r.snd.reverse.reverse)) g_rules =
    g_rules
  simp [List.reverse_reverse]

private lemma derives_reversed (g : CFgrammar T) (v : List (Symbol T g.nt)) :
  (reversalGrammar g).Derives [Symbol.nonterminal (reversalGrammar g).initial] v →
    g.Derives [Symbol.nonterminal g.initial] v.reverse :=
by
  intro hv
  induction' hv with u w _ orig ih
  · rw [List.reverse_singleton]
    apply CFgrammar.deri_self
  apply CFgrammar.deri_of_deri_tran ih
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
  · rw [← List.reverse_singleton, ← List.reverse_append_append]
    have fst_from_r : r₀.fst = r.fst
    · rw [← r_from_r₀]
    rw [fst_from_r]
    exact congr_arg List.reverse bef
  · have snd_from_r : r₀.snd = r.snd.reverse
    · rw [← r_from_r₀, List.reverse_reverse]
    rw [snd_from_r, ← List.reverse_append_append]
    exact congr_arg List.reverse aft

private lemma reversed_word_in_original_language {g : CFgrammar T} {w : List T}
    (hyp : w ∈ (reversalGrammar g).language) :
  w.reverse ∈ g.language :=
by
  unfold CFgrammar.language at *
  rw [Set.mem_setOf_eq] at *
  unfold CFgrammar.Generates at *
  rw [List.map_reverse]
  exact derives_reversed g (List.map Symbol.terminal w) hyp

/-- The class of context-free languages is closed under reversal. -/
theorem CF_of_reverse_CF (L : Language T) :
  IsCF L → IsCF (reverseLang L) :=
by
  rintro ⟨g, hgL⟩
  rw [← hgL]
  use reversalGrammar g
  unfold reverseLang
  apply Set.eq_of_subset_of_subset
  · intro w hwL
    exact reversed_word_in_original_language hwL
  · intro w hwL
    have pre_reversal : ∃ g₀, g = reversalGrammar g₀
    · use reversalGrammar g
      rw [dual_of_reversalGrammar]
    cases' pre_reversal with g₀ pre_rev
    rw [pre_rev] at hwL ⊢
    have finished_modulo_reverses := reversed_word_in_original_language hwL
    rw [dual_of_reversalGrammar]
    rw [List.reverse_reverse] at finished_modulo_reverses
    exact finished_modulo_reverses
