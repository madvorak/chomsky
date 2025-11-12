import Chomsky.Classes.ContextFree.Basics.Toolbox
import Chomsky.Utilities.ListUtils

variable {T : Type}


/-- Context-free grammar for the empty language (i.e., `∈` always gives `false`). -/
def cfgEmptyLang : CFG T :=
  CFG.mk (Fin 1) 0 []

/-- Characterization of the empty language. -/
lemma language_of_cfgEmptyLang : CFG.language (@cfgEmptyLang T) = 0 :=
  by
  unfold CFG.language
  ext1 w
  constructor; swap
  · intro h
    exfalso
    exact Set.not_mem_empty w h
  intro hw
  sorry /-
  change
    CFDerives cfgEmptyLang [Symbol.nonterminal cfg_empty_lang.initial]
      (List.map Symbol.terminal w) at hw
  exfalso
  cases CF_eq_or_tran_deri_of_deri hw
  · have hhead := congr_fun (congr_arg List.get? h) 0
    cases' w with head tail ih
    · change some (Symbol.nonterminal cfg_empty_lang.initial) = none at hhead
      norm_cast at hhead
    · change some (Symbol.nonterminal cfg_empty_lang.initial) = some (Symbol.terminal head) at hhead
      norm_cast at hhead
  · rcases h with ⟨v, ⟨r, rin, -, -, -, -⟩, -⟩
    cases rin -/

/-- Context-free grammar for the singleton language that contains `[]` as its only word. -/
def cfgEmptyWord : CFG T :=
  CFG.mk (Fin 1) 0 [(0, [])]

/-- Characterization of the singleton language. -/
lemma language_of_cfgEmptyWord : CFG.language (@cfgEmptyWord T) = singleton [] :=
  by
  unfold CFG.language
  ext1 w
  sorry /-
  constructor; swap
  · intro h
    rw [Set.mem_singleton_iff] at h
    change
      CFDerives cfgEmptyWord [Symbol.nonterminal cfg_empty_lang.initial]
        (List.map Symbol.terminal w)
    apply @CF_deri_of_tran
    use ((0 : Fin 1), [])
    use [], []
    rw [h]
    constructor <;> rfl
    exact T
  intro hw
  change
    CFDerives (@cfgEmptyWord T) [Symbol.nonterminal (@cfgEmptyLang T).initial]
      (List.map Symbol.terminal w) at hw
  cases
    @CF_eq_or_tran_deri_of_deri T (@cfgEmptyWord T) [Symbol.nonterminal cfg_empty_lang.initial]
      (List.map Symbol.terminal w) hw
  · exfalso
    have zeroth := congr_fun (congr_arg List.get? h) 0
    rw [List.get?] at zeroth
    by_cases w = List.nil
    · have is_none : (List.map Symbol.terminal w).get? 0 = none :=
        by
        rw [h]
        rw [List.get?_map]
        rfl
      rw [is_none] at zeroth
      exact Option.noConfusion zeroth
    · have is_terminal : ∃ t, (List.map Symbol.terminal w).get? 0 = some (Symbol.terminal t) :=
        by
        apply Exists.intro (w.nth_le 0 (List.length_pos_of_ne_nil h))
        rw [List.get?_map]
        norm_num
        exact List.nthLe_get? (List.length_pos_of_ne_nil h)
      cases' is_terminal with irr is_termin
      rw [is_termin] at zeroth
      norm_cast at zeroth
  rcases h with ⟨v, step_init, step_none⟩
  have v_is_empty_word : v = List.nil :=
    by
    rcases step_init with ⟨r, rin, pre, pos, bef, aft⟩
    have rule : r = ((0 : Fin 1), []) :=
      by
      rw [←List.mem_singleton]
      exact rin
    have empty_surrounding : pre = [] ∧ Pos = [] :=
      by
      rw [rule] at bef
      have bef_lenghts := congr_arg List.length bef
      rw [List.length_append_append] at bef_lenghts
      rw [List.length_singleton] at bef_lenghts
      rw [List.length_singleton] at bef_lenghts
      constructor
      · have pre_zero : pre.length = 0 := by
          clear * - bef_lenghts
          linarith
        rw [List.length_eq_zero] at pre_zero
        exact pre_zero
      · have pos_zero : pos.length = 0 := by
          clear * - bef_lenghts
          linarith
        rw [List.length_eq_zero] at pos_zero
        exact pos_zero
    rw [empty_surrounding.1] at aft
    rw [empty_surrounding.2] at aft
    rw [rule] at aft
    exact aft
  rw [v_is_empty_word] at step_none
  cases @CF_eq_or_tran_deri_of_deri T (@cfgEmptyWord T) List.nil (List.map Symbol.terminal w) step_none
  · by_contra contra
    have w_not_nil : w.length > 0 :=
      by
      apply List.length_pos_of_ne_nil
      convert contra
    have impossible_lengths := congr_arg List.length h
    rw [List.length] at impossible_lengths
    rw [List.length_map] at impossible_lengths
    rw [←impossible_lengths] at w_not_nil
    exact Nat.lt_irrefl 0 w_not_nil
  · exfalso
    rcases h with ⟨-, ⟨trash_r, -, trash_1, trash_2, impossible, -⟩, -⟩
    have impossible_len := congr_arg List.length impossible
    clear * - impossible_len
    rw [List.length_append_append] at impossible_len
    rw [List.length_singleton] at impossible_len
    rw [List.length] at impossible_len
    linarith -/

/-- Context-free grammar for a language `{a}.star` where `a` is a given terminal symbol. -/
def cfgSymbolStar (a : T) : CFG T :=
  CFG.mk (Fin 1) 0 [(0, [Symbol.terminal a, Symbol.nonterminal 0]), (0, [])]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Characterization of the `{a}.star` language. -/
lemma language_of_cfgSymbolStar (a : T) :
    (cfgSymbolStar a).language = fun w => ∃ n : ℕ, w = List.replicate n a :=
  by sorry /-
  apply Set.eq_of_subset_of_subset
  · intro w
    /-
          We prove this inclusion as follows:
          (1) `w ∈ CF_language (cfg_symbol_star a)` →
          (2) `w` contains only `a`s →
          (3) `∃ (n : ℕ), w = list.replicate a n)` □
    -/
    have implication2 : (∀ t : T, t ≠ a → t ∉ w) → ∃ n : ℕ, w = List.replicate n a :=
      by
      contrapose
      intro contr ass
      push_neg at contr
      specialize contr w.length
      have different :
        ∃ n : ℕ,
          ∃ hl : n < w.length,
            ∃ hr : n < (List.replicate w.length a).length,
              w.nth_le n hl ≠ (List.replicate w.length a).nthLe n hr :=
        by
        by_contra isnt
        have same_len : w.length = (List.replicate w.length a).length := by
          rw [List.length_replicate]
        apply contr
        apply List.ext_nthLe same_len
        push_neg at isnt
        intro n n_small_left n_small_right
        specialize isnt n n_small_left
        push_neg at isnt
        specialize isnt n_small_right
        push_neg at isnt
        exact isnt
      rcases different with ⟨n, hl, hr, nq⟩
      rw [List.nthLe_replicate a hr] at nq
      specialize ass (w.nth_le n hl) nq
      exact ass (List.nthLe_mem w n hl)
    have implication1 : w ∈ (cfgSymbolStar a).language → ∀ t : T, t ≠ a → t ∉ w :=
      by sorry /-
      clear implication2
      intro ass t nq
      change CFGeneratesStr (cfgSymbolStar a) (List.map Symbol.terminal w) at ass
      unfold CFGeneratesStr at ass
      have indu :
        ∀ v : List (Symbol T (cfgSymbolStar a).nt),
          CFDerives (cfgSymbolStar a) [Symbol.nonterminal (cfgSymbolStar a).initial] v →
            Symbol.terminal t ∉ v :=
        by
        intro v hyp
        induction' hyp with x y trash orig ih
        · clear * -
          rw [List.mem_singleton]
          apply Symbol.noConfusion
        rcases orig with ⟨r, rin, p, q, bef, aft⟩
        rw [aft]
        rw [bef] at ih
        repeat' rw [List.mem_append] at *
        push_neg
        push_neg at ih
        constructor; swap
        · exact ih.right
        constructor
        · exact ih.left.left
        cases rin
        · rw [rin]
          dsimp only
          intro imposs
          cases imposs
          · apply nq
            exact Symbol.terminal.inj imposs
          cases imposs
          · norm_cast at imposs
          exact List.not_mem_nil (@Symbol.terminal T (cfgSymbolStar a).nt t) imposs
        · change r ∈ [((0 : Fin 1), ([] : List (Symbol T (cfgSymbolStar a).nt)))] at rin
          rw [List.mem_singleton] at rin
          rw [rin]
          exact List.not_mem_nil (Symbol.terminal t)
      specialize indu (List.map Symbol.terminal w) ass
      by_contra contra
      exact indu (List.mem_map_of_mem Symbol.terminal contra) -/
    exact implication2 ∘ implication1
  · intro w hw
    cases' hw with n hwn
    rw [hwn]
    convert_to CFGeneratesStr (cfgSymbolStar a) (List.map Symbol.terminal (List.replicate n a))
    unfold CFGeneratesStr
    clear hwn w
    have comes_to :
      CFDerives (cfgSymbolStar a) [Symbol.nonterminal (cfgSymbolStar a).initial]
        (List.replicate n (Symbol.terminal a) ++ [Symbol.nonterminal (0 : Fin 1)]) :=
      by
      induction' n with n ih
      · apply CF_deri_self
      apply CF_deri_of_deri_tran ih
      use ((0 : Fin 1), [Symbol.terminal a, Symbol.nonterminal (0 : Fin 1)])
      constructor
      · apply List.mem_cons_self
      use List.replicate n (Symbol.terminal a), []
      constructor
      · rw [List.append_nil]
      rw [List.append_nil]
      change
        (Symbol.terminal
              a::List.replicate n (Symbol.terminal a) ++ [Symbol.nonterminal (0 : Fin 1)]) =
          List.replicate n (Symbol.terminal a) ++ ([Symbol.terminal a] ++ [Symbol.nonterminal 0])
      sorry /-
      rw [←List.cons_append]
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
      have count_succ_left :
        (@Symbol.terminal T (Fin 1) a::List.replicate n (Symbol.terminal a)) =
          List.replicate (n + 1) (Symbol.terminal a) :=
        by
        symm
        apply List.replicate_succ
      have count_succ_right :
        List.replicate n (Symbol.terminal a) ++ [Symbol.terminal a] =
          List.replicate (n + 1) (Symbol.terminal a) :=
        by
        change
          List.replicate n (Symbol.terminal a) ++ List.replicate 1 (Symbol.terminal a) =
            List.replicate (n + 1) (Symbol.terminal a)
        symm
        apply List.replicate_add
      rw [count_succ_left]
      rw [count_succ_right] -/
    apply CF_deri_of_deri_tran comes_to
    use ((0 : Fin 1), [])
    constructor
    · apply List.mem_cons_of_mem
      apply List.mem_cons_self
    use List.replicate n (Symbol.terminal a), []
    constructor <;> simp -/
