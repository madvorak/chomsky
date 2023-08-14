import Grammars.Classes.Unrestricted.Basics.Toolbox
import Grammars.Utilities.LanguageOperations
import Grammars.Utilities.ListUtils

variable {T : Type}

section Auxiliary

private def reversalGrule {N : Type} (r : Grule T N) : Grule T N :=
  Grule.mk r.inputR.reverse r.inputN r.inputL.reverse r.output.reverse

private lemma dual_of_reversal_grule {N : Type} (r : Grule T N) :
  reversalGrule (reversalGrule r) = r :=
by
  cases r
  unfold reversalGrule
  dsimp only
  simp [List.reverse_reverse]

private lemma reversal_grule_reversal_grule {N : Type} :
  @reversalGrule T N ∘ @reversalGrule T N = id :=
by
  ext
  apply dual_of_reversal_grule

private def reversalGrammar (g : Grammar T) : Grammar T :=
  Grammar.mk g.nt g.initial (List.map reversalGrule g.rules)

private lemma dual_of_reversalGrammar (g : Grammar T) :
  reversalGrammar (reversalGrammar g) = g :=
by
  cases g
  unfold reversalGrammar
  dsimp only
  rw [List.map_map]
  rw [reversal_grule_reversal_grule]
  rw [List.map_id]

private lemma derives_reversed (g : Grammar T) (v : List (Symbol T g.nt)) :
  (reversalGrammar g).Derives [Symbol.nonterminal (reversalGrammar g).initial] v →
    g.Derives [Symbol.nonterminal g.initial] v.reverse :=
by
  intro hv
  induction' hv with u w _ orig ih
  · rw [List.reverse_singleton]
    apply Grammar.deri_self
  apply Grammar.deri_of_deri_tran ih
  rcases orig with ⟨r, rin, x, y, bef, aft⟩
  change r ∈ List.map _ g.rules at rin 
  rw [List.mem_map] at rin 
  rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
  use r₀
  constructor
  · exact rin₀
  use y.reverse
  use x.reverse
  constructor
  · have rid₁ : r₀.inputL = r.inputR.reverse
    · rw [← r_from_r₀]
      unfold reversalGrule
      rw [List.reverse_reverse]
    have rid₂ : [Symbol.nonterminal r₀.inputN] = [Symbol.nonterminal r.inputN].reverse
    · rw [← r_from_r₀]
      rw [List.reverse_singleton]
      rfl
      exact T
    have rid₃ : r₀.inputR = r.inputL.reverse
    · rw [← r_from_r₀]
      unfold reversalGrule
      rw [List.reverse_reverse]
    rw [rid₁, rid₂, rid₃, ← List.reverse_append_append, ← List.reverse_append_append, ←
      List.append_assoc, ← List.append_assoc]
    congr
  · have snd_from_r : r₀.output = r.output.reverse
    · rw [← r_from_r₀]
      unfold reversalGrule
      rw [List.reverse_reverse]
    rw [snd_from_r]
    rw [← List.reverse_append_append]
    exact congr_arg List.reverse aft

private lemma reversed_word_in_original_language {g : Grammar T} {w : List T}
    (hyp : w ∈ (reversalGrammar g).language) :
  w.reverse ∈ g.language :=
by
  unfold Grammar.language at *
  have almost_done := derives_reversed g (List.map Symbol.terminal w) hyp
  rw [← List.map_reverse] at almost_done 
  exact almost_done

end Auxiliary

/-- The class of grammar-generated languages is closed under reversal. -/
theorem GG_of_reverse_GG (L : Language T) :
  IsGG L → IsGG (reverseLang L) :=
by
  rintro ⟨g, hgL⟩
  rw [← hgL]
  use reversalGrammar g
  unfold reverseLang
  apply Set.eq_of_subset_of_subset
  · intro w hwL
    change w.reverse ∈ g.language
    exact reversed_word_in_original_language hwL
  · intro w hwL
    change w.reverse ∈ g.language at hwL 
    obtain ⟨g₀, pre_reversal⟩ : ∃ g₀, g = reversalGrammar g₀
    · use reversalGrammar g
      rw [dual_of_reversalGrammar]
    rw [pre_reversal] at hwL ⊢
    have finished_up_to_reverses := reversed_word_in_original_language hwL
    rw [dual_of_reversalGrammar]
    rw [List.reverse_reverse] at finished_up_to_reverses 
    exact finished_up_to_reverses
