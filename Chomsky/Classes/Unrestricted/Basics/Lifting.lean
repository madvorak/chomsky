import Chomsky.Classes.Unrestricted.Basics.Toolbox
import Chomsky.Utilities.ListUtils


section functions_lift_sink

variable {T N₀ N : Type}

def liftSymbol (liftN : N₀ → N) : Symbol T N₀ → Symbol T N
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (liftN n)

def sinkSymbol (sinkN : N → Option N₀) : Symbol T N → Option (Symbol T N₀)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal n => Option.map Symbol.nonterminal (sinkN n)

def liftString (liftN : N₀ → N) : List (Symbol T N₀) → List (Symbol T N) :=
  List.map (liftSymbol liftN)

def sinkString (sinkN : N → Option N₀) : List (Symbol T N) → List (Symbol T N₀) :=
  List.filterMap (sinkSymbol sinkN)

def liftRule (liftN : N₀ → N) : Grule T N₀ → Grule T N :=
  fun r : Grule T N₀ => Grule.mk
    (liftString liftN r.inputL)
    (liftN r.inputN)
    (liftString liftN r.inputR)
    (liftString liftN r.output)

end functions_lift_sink


section lifting_conditions

structure LiftedGrammar (T : Type) where
  g₀: Grammar T
  g : Grammar T
  liftNt : g₀.nt → g.nt
  sinkNt : g.nt → Option g₀.nt
  lift_inj : liftNt.Injective
  sink_inj : ∀ x y, sinkNt x = sinkNt y → x = y ∨ sinkNt x = none
  sinkNt_liftNt : ∀ n₀ : g₀.nt, sinkNt (liftNt n₀) = some n₀
  corresponding_rules : ∀ r : Grule T g₀.nt, r ∈ g₀.rules → liftRule liftNt r ∈ g.rules
  preimage_of_rules :
    ∀ r : Grule T g.nt,
      (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, liftNt n₀ = r.inputN) →
        (∃ r₀ ∈ g₀.rules, liftRule liftNt r₀ = r)

private lemma lifted_grammar_inverse {T : Type} (G : LiftedGrammar T) :
  ∀ x : G.g.nt, (∃ n₀, G.sinkNt x = some n₀) → (Option.map G.liftNt (G.sinkNt x) = x) :=
by
  intro x h
  cases' h with n₀ ass
  rw [ass, Option.map_some']
  apply congr_arg
  symm
  by_contra x_neq
  have inje := G.sink_inj x (G.liftNt n₀)
  rw [G.sinkNt_liftNt] at inje
  cases' inje ass with case_valu case_none
  · exact x_neq case_valu
  rw [ass] at case_none
  exact Option.noConfusion case_none

end lifting_conditions


section translating_derivations

variable {T : Type}

private lemma lift_tran {G : LiftedGrammar T} {w₁ w₂ : List (Symbol T G.g₀.nt)}
    (hGww : G.g₀.Transforms w₁ w₂) :
  G.g.Transforms (liftString G.liftNt w₁) (liftString G.liftNt w₂) :=
by
  rcases hGww with ⟨r, rin, u, v, bef, aft⟩
  use liftRule G.liftNt r
  constructor
  · exact G.corresponding_rules r rin
  use liftString G.liftNt u
  use liftString G.liftNt v
  constructor
  · have lift_bef := congr_arg (liftString G.liftNt) bef
    unfold liftString at *
    rw [List.map_append_append, List.map_append_append] at lift_bef
    exact lift_bef
  · have lift_aft := congr_arg (liftString G.liftNt) aft
    unfold liftString at *
    rw [List.map_append_append] at lift_aft
    exact lift_aft

lemma lift_deri (G : LiftedGrammar T) {w₁ w₂ : List (Symbol T G.g₀.nt)}
    (hGww : G.g₀.Derives w₁ w₂) :
  G.g.Derives (liftString G.liftNt w₁) (liftString G.liftNt w₂) :=
by
  induction' hGww with u v _ orig ih
  · apply gr_deri_self
  apply gr_deri_of_deri_tran
  · exact ih
  exact lift_tran orig

def GoodLetter {G : LiftedGrammar T} : Symbol T G.g.nt → Prop
  | Symbol.terminal _ => True
  | Symbol.nonterminal n => ∃ n₀ : G.g₀.nt, G.sinkNt n = n₀

def GoodString {G : LiftedGrammar T} (s : List (Symbol T G.g.nt)) : Prop :=
  ∀ a ∈ s, GoodLetter a

private lemma sink_tran {G : LiftedGrammar T} {w₁ w₂ : List (Symbol T G.g.nt)}
    (hGww : G.g.Transforms w₁ w₂) (ok_input : GoodString w₁) :
  G.g₀.Transforms (sinkString G.sinkNt w₁) (sinkString G.sinkNt w₂) ∧ GoodString w₂ :=
by
  rcases hGww with ⟨r, rin, u, v, bef, aft⟩
  rcases G.preimage_of_rules r (by
      constructor
      · exact rin
      rw [bef] at ok_input
      have good_matched_nonterminal : GoodLetter (Symbol.nonterminal r.inputN)
      · apply ok_input (Symbol.nonterminal r.inputN)
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        rw [List.mem_singleton]
      change ∃ n₀ : G.g₀.nt, G.sinkNt r.inputN = some n₀ at good_matched_nonterminal
      cases' good_matched_nonterminal with n₀ hn₀
      use n₀
      have almost := congr_arg (Option.map G.liftNt) hn₀
      rw [lifted_grammar_inverse G r.inputN ⟨n₀, hn₀⟩] at almost
      rw [Option.map_some'] at almost
      apply Option.some_injective
      exact almost.symm
    )
    with ⟨r₀, pre_in, preimage⟩
  constructor; swap
  · rw [bef] at ok_input
    rw [aft]
    unfold GoodString at ok_input ⊢
    rw [← preimage]
    clear * - ok_input
    rw [List.forall_mem_append_append] at ok_input ⊢
    rw [List.forall_mem_append_append] at ok_input
    constructor
    · exact ok_input.left.left
    constructor; swap
    · exact ok_input.right.right
    intro a a_in_ros
    cases a
    · simp [GoodLetter]
    unfold liftRule at a_in_ros
    dsimp only at a_in_ros
    unfold liftString at a_in_ros
    rw [List.mem_map] at a_in_ros
    rcases a_in_ros with ⟨s, trash, a_from_s⟩
    rw [← a_from_s]
    cases' s with s' s''
    · exfalso
      clear * - a_from_s
      unfold liftSymbol at a_from_s
      exact Symbol.noConfusion a_from_s
    simp [liftSymbol, GoodLetter]
    use s''
    exact G.sinkNt_liftNt s''
  use r₀
  constructor
  · exact pre_in
  use sinkString G.sinkNt u
  use sinkString G.sinkNt v
  have correct_inverse : sinkSymbol G.sinkNt ∘ liftSymbol G.liftNt = Option.some
  · ext1 x
    cases x
    · rfl
    rw [Function.comp_apply]
    simp [liftSymbol, sinkSymbol]
    rw [G.sinkNt_liftNt]
    exact T
  constructor
  · have sink_bef := congr_arg (sinkString G.sinkNt) bef
    unfold sinkString at *
    rw [List.filterMap_append_append] at sink_bef
    rw [List.filterMap_append_append] at sink_bef
    convert sink_bef <;> rw [← preimage] <;> unfold liftRule <;> dsimp only <;> clear * - correct_inverse
    · unfold liftString
      rw [List.filterMap_map]
      rw [correct_inverse]
      rw [List.filterMap_some]
    · change
        [Symbol.nonterminal r₀.inputN] =
        List.filterMap (sinkSymbol G.sinkNt) (List.map (liftSymbol G.liftNt) [Symbol.nonterminal r₀.inputN])
      rw [List.filterMap_map, correct_inverse, List.filterMap_some]
    · unfold liftString
      rw [List.filterMap_map, correct_inverse, List.filterMap_some]
  · have sink_aft := congr_arg (sinkString G.sinkNt) aft
    unfold sinkString at *
    rw [List.filterMap_append_append] at sink_aft
    convert sink_aft
    rw [← preimage]
    clear * - correct_inverse
    unfold liftRule
    dsimp only
    unfold liftString
    rw [List.filterMap_map, correct_inverse, List.filterMap_some]

private lemma sink_deri_aux {G : LiftedGrammar T} {w₁ w₂ : List (Symbol T G.g.nt)}
    (hGww : G.g.Derives w₁ w₂) (ok_input : GoodString w₁) :
  G.g₀.Derives (sinkString G.sinkNt w₁) (sinkString G.sinkNt w₂) ∧ GoodString w₂ :=
by
  induction' hGww with u v _ orig ih
  · constructor
    · apply gr_deri_self
    · exact ok_input
  have both := sink_tran orig ih.right
  constructor; swap
  · exact both.right
  apply gr_deri_of_deri_tran
  · exact ih.left
  · exact both.left

lemma sink_deri (G : LiftedGrammar T) {w₁ w₂ : List (Symbol T G.g.nt)}
    (hGww : G.g.Derives w₁ w₂) (ok_input : GoodString w₁) :
  G.g₀.Derives (sinkString G.sinkNt w₁) (sinkString G.sinkNt w₂) :=
(sink_deri_aux hGww ok_input).left

end translating_derivations
