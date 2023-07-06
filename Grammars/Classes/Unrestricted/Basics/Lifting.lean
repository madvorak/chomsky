import Grammars.Classes.Unrestricted.Basics.Toolbox
import Grammars.Utilities.ListUtils


section FunctionsLiftSink

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

end FunctionsLiftSink


section LiftingConditions

structure LiftedGrammar (T : Type) where
  g₀ : Grammar T
  g : Grammar T
  liftNt : g₀.nt → g.nt
  sinkNt : g.nt → Option g₀.nt
  lift_inj : Function.Injective liftNt
  sink_inj : ∀ x y,  sinkNt x = sinkNt y  →  x = y  ∨  sinkNt x = none
  sinkNt_liftNt : ∀ n₀ : g₀.nt, sinkNt (liftNt n₀) = some n₀
  corresponding_rules : ∀ r : Grule T g₀.nt,  r ∈ g₀.rules  →  liftRule liftNt r ∈ g.rules
  preimage_of_rules :
    ∀ r : Grule T g.nt,
      (r ∈ g.rules  ∧  ∃ n₀ : g₀.nt, liftNt n₀ = r.inputN) →
        (∃ r₀ ∈ g₀.rules, liftRule liftNt r₀ = r)

private lemma lifted_grammar_inverse {T : Type} (lg : LiftedGrammar T) :
  ∀ x : lg.g.nt, (∃ n₀, lg.sinkNt x = some n₀) → (Option.map lg.liftNt (lg.sinkNt x) = x) :=
by
  intro x h
  cases' h with n₀ ass
  rw [ass, Option.map_some']
  apply congr_arg
  symm
  by_contra x_neq
  have inje := lg.sink_inj x (lg.liftNt n₀)
  rw [lg.sinkNt_liftNt] at inje 
  cases' inje ass with case_valu case_none
  · exact x_neq case_valu
  rw [ass] at case_none 
  exact Option.noConfusion case_none

end LiftingConditions


section TranslatingDerivations

variable {T : Type}

private lemma lift_tran {lg : LiftedGrammar T} {w₁ w₂ : List (Symbol T lg.g₀.nt)}
    (hyp : Grammar.Transforms lg.g₀ w₁ w₂) :
  Grammar.Transforms lg.g (liftString lg.liftNt w₁) (liftString lg.liftNt w₂) :=
by
  rcases hyp with ⟨r, rin, u, v, bef, aft⟩
  use liftRule lg.liftNt r
  constructor
  · exact lg.corresponding_rules r rin
  use liftString lg.liftNt u
  use liftString lg.liftNt v
  constructor
  · have lift_bef := congr_arg (liftString lg.liftNt) bef
    unfold liftString at *
    rw [List.map_append_append, List.map_append_append] at lift_bef 
    exact lift_bef
  · have lift_aft := congr_arg (liftString lg.liftNt) aft
    unfold liftString at *
    rw [List.map_append_append] at lift_aft
    exact lift_aft

lemma lift_deri (lg : LiftedGrammar T) {w₁ w₂ : List (Symbol T lg.g₀.nt)}
    (hyp : Grammar.Derives lg.g₀ w₁ w₂) :
  Grammar.Derives lg.g (liftString lg.liftNt w₁) (liftString lg.liftNt w₂) :=
by
  induction' hyp with u v _ orig ih
  · apply Grammar.deri_self
  apply Grammar.deri_of_deri_tran
  · exact ih
  exact lift_tran orig

def GoodLetter {lg : LiftedGrammar T} : Symbol T lg.g.nt → Prop
  | Symbol.terminal _ => True
  | Symbol.nonterminal n => ∃ n₀ : lg.g₀.nt, lg.sinkNt n = n₀

def GoodString {lg : LiftedGrammar T} (s : List (Symbol T lg.g.nt)) : Prop :=
  ∀ a ∈ s, GoodLetter a

private lemma sink_tran {lg : LiftedGrammar T} {w₁ w₂ : List (Symbol T lg.g.nt)}
    (hyp : Grammar.Transforms lg.g w₁ w₂) (ok_input : GoodString w₁) :
  Grammar.Transforms lg.g₀ (sinkString lg.sinkNt w₁) (sinkString lg.sinkNt w₂) ∧ GoodString w₂ :=
by
  rcases hyp with ⟨r, rin, u, v, bef, aft⟩
  rcases lg.preimage_of_rules r (by
      constructor
      · exact rin
      rw [bef] at ok_input 
      have good_matched_nonterminal : GoodLetter (Symbol.nonterminal r.inputN)
      · apply ok_input (Symbol.nonterminal r.inputN)
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        rw [List.mem_singleton]
      change ∃ n₀ : lg.g₀.nt, lg.sinkNt r.inputN = some n₀ at good_matched_nonterminal 
      cases' good_matched_nonterminal with n₀ hn₀
      use n₀
      have almost := congr_arg (Option.map lg.liftNt) hn₀
      rw [lifted_grammar_inverse lg r.inputN ⟨n₀, hn₀⟩] at almost 
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
    · exact ok_input.1.1
    constructor; swap
    · exact ok_input.2.2
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
    exact lg.sinkNt_liftNt s''
  use r₀
  constructor
  · exact pre_in
  use sinkString lg.sinkNt u
  use sinkString lg.sinkNt v
  have correct_inverse : sinkSymbol lg.sinkNt ∘ liftSymbol lg.liftNt = Option.some
  · ext1 x
    cases x
    · rfl
    rw [Function.comp_apply]
    simp [liftSymbol, sinkSymbol]
    rw [lg.sinkNt_liftNt]
    exact T
  constructor
  · have sink_bef := congr_arg (sinkString lg.sinkNt) bef
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
        List.filterMap (sinkSymbol lg.sinkNt) (List.map (liftSymbol lg.liftNt) [Symbol.nonterminal r₀.inputN])
      rw [List.filterMap_map, correct_inverse, List.filterMap_some]
    · unfold liftString
      rw [List.filterMap_map, correct_inverse, List.filterMap_some]
  · have sink_aft := congr_arg (sinkString lg.sinkNt) aft
    unfold sinkString at *
    rw [List.filterMap_append_append] at sink_aft 
    convert sink_aft
    rw [← preimage]
    clear * - correct_inverse
    unfold liftRule
    dsimp only
    unfold liftString
    rw [List.filterMap_map, correct_inverse, List.filterMap_some]

private lemma sink_deri_aux {lg : LiftedGrammar T} {w₁ w₂ : List (Symbol T lg.g.nt)}
    (hyp : Grammar.Derives lg.g w₁ w₂) (ok_input : GoodString w₁) :
  Grammar.Derives lg.g₀ (sinkString lg.sinkNt w₁) (sinkString lg.sinkNt w₂) ∧ GoodString w₂ :=
by
  induction' hyp with u v _ orig ih
  · constructor
    · apply Grammar.deri_self
    · exact ok_input
  have both := sink_tran orig ih.2
  constructor; swap
  · exact both.2
  apply Grammar.deri_of_deri_tran
  · exact ih.1
  · exact both.1

lemma sink_deri (lg : LiftedGrammar T) {w₁ w₂ : List (Symbol T lg.g.nt)}
    (hyp : Grammar.Derives lg.g w₁ w₂) (ok_input : GoodString w₁) :
  Grammar.Derives lg.g₀ (sinkString lg.sinkNt w₁) (sinkString lg.sinkNt w₂) :=
(sink_deri_aux hyp ok_input).1

end TranslatingDerivations
