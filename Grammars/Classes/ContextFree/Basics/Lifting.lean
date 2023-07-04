/-import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.ListUtils

variable {T : Type}

def liftSymbol {N₀ N : Type} (lift_N : N₀ → N) : Symbol T N₀ → Symbol T N
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (lift_N n)

def sinkSymbol {N₀ N : Type} (sink_N : N → Option N₀) : Symbol T N → Option (Symbol T N₀)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal n => Option.map Symbol.nonterminal (sink_N n)

def liftString {N₀ N : Type} (lift_N : N₀ → N) : List (Symbol T N₀) → List (Symbol T N) :=
  List.map (liftSymbol lift_N)

def sinkString {N₀ N : Type} (sink_N : N → Option N₀) : List (Symbol T N) → List (Symbol T N₀) :=
  List.filterMap (sinkSymbol sink_N)

def liftRule {N₀ N : Type} (lift_N : N₀ → N) : N₀ × List (Symbol T N₀) → N × List (Symbol T N) :=
  fun r => (lift_N r.fst, liftString lift_N r.snd)

structure LiftedGrammar where
  (g₀ g : CFgrammar T)
  liftNt : g₀.nt → g.nt
  lift_inj : Function.Injective liftNt
  corresponding_rules :
    ∀ r : g₀.nt × List (Symbol T g₀.nt), r ∈ g₀.rules → liftRule liftNt r ∈ g.rules
  sinkNt : g.nt → Option g₀.nt
  sink_inj : ∀ x y, sinkNt x = sinkNt y → x = y ∨ sinkNt x = none
  preimage_of_rules :
    ∀ r : g.nt × List (Symbol T g.nt),
      (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, liftNt n₀ = r.fst) → ∃ r₀ ∈ g₀.rules, liftRule liftNt r₀ = r
  liftNt_sink : ∀ n₀ : g₀.nt, sinkNt (liftNt n₀) = some n₀

private lemma lifted_grammar_inverse (lg : @LiftedGrammar T) :
    ∀ x : lg.g.nt, (∃ val, lg.sinkNt x = some val) → Option.map lg.liftNt (lg.sinkNt x) = x :=
  by
  intro x h
  cases' h with valu ass
  rw [ass]
  rw [Option.map_some']
  apply congr_arg
  symm
  by_contra
  have inje := lg.sink_inj x (lg.liftNt valu)
  rw [lg.liftNt_sink] at inje 
  cases' inje ass with case_valu case_none
  · exact h case_valu
  rw [ass] at case_none 
  exact Option.noConfusion case_none

private lemma lift_tran {lg : LiftedGrammar} {w₁ w₂ : List (Symbol T lg.g₀.nt)}
    (hyp : CFTransforms lg.g₀ w₁ w₂) :
    CFTransforms lg.g (liftString lg.liftNt w₁) (liftString lg.liftNt w₂) :=
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
    rw [List.map_append_append] at lift_bef 
    convert lift_bef
  · have lift_aft := congr_arg (liftString lg.liftNt) aft
    unfold liftString at *
    rw [List.map_append_append] at lift_aft 
    exact lift_aft

lemma lift_deri {lg : LiftedGrammar} {w₁ w₂ : List (Symbol T lg.g₀.nt)}
    (hyp : CFDerives lg.g₀ w₁ w₂) :
    CFDerives lg.g (liftString lg.liftNt w₁) (liftString lg.liftNt w₂) :=
  by
  induction' hyp with x y trash orig ih
  · apply CF_deri_self
  apply CF_deri_of_deri_tran
  · exact ih
  exact lift_tran orig

def GoodLetter {lg : @LiftedGrammar T} : Symbol T lg.g.nt → Prop
  | Symbol.terminal t => True
  | Symbol.nonterminal n => ∃ n₀ : lg.g₀.nt, lg.sinkNt n = n₀

def GoodString {lg : @LiftedGrammar T} (s : List (Symbol T lg.g.nt)) :=
  ∀ a ∈ s, GoodLetter a

private lemma sink_tran {lg : LiftedGrammar} {w₁ w₂ : List (Symbol T lg.g.nt)}
    (hyp : CFTransforms lg.g w₁ w₂) (ok_input : GoodString w₁) :
    CFTransforms lg.g₀ (sinkString lg.sinkNt w₁) (sinkString lg.sinkNt w₂) :=
  by
  rcases hyp with ⟨r, rin, u, v, bef, aft⟩
  rcases lg.preimage_of_rules r
      (by
        constructor
        · exact rin
        rw [bef] at ok_input 
        have good_matched_nonterminal : GoodLetter (Symbol.nonterminal r.fst) :=
          by
          specialize ok_input (Symbol.nonterminal r.fst)
          unfold GoodLetter
          sorry
        change ∃ n₀ : lg.g₀.nt, lg.sinkNt r.fst = some n₀ at good_matched_nonterminal 
        cases' good_matched_nonterminal with n₀ hn₀
        use n₀
        have almost := congr_arg (Option.map lg.liftNt) hn₀
        rw [lifted_grammar_inverse lg r.fst ⟨n₀, hn₀⟩] at almost 
        rw [Option.map_some'] at almost 
        apply Option.some_injective
        exact almost.symm) with
    ⟨p, pin, preimage⟩
  use p
  constructor
  · exact pin
  use sinkString lg.sinkNt u
  use sinkString lg.sinkNt v
  have correct_inverse : sinkSymbol lg.sinkNt ∘ liftSymbol lg.liftNt = Option.some :=
    by
    ext1 x
    cases x
    · rfl
    rw [Function.comp_apply]
    unfold liftSymbol
    unfold sinkSymbol
    rw [lg.liftNt_sink]
    apply Option.map_some'
  constructor
  · have sink_bef := congr_arg (sinkString lg.sinkNt) bef
    unfold sinkString at *
    rw [List.filterMap_append_append] at sink_bef 
    convert sink_bef
    rw [← preimage]
    unfold liftRule
    dsimp only
    change
      [Symbol.nonterminal p.fst] =
        List.filterMap (sinkSymbol lg.sinkNt)
          (List.map (liftSymbol lg.liftNt) [Symbol.nonterminal p.fst])
    rw [List.filterMap_map]
    rw [correct_inverse]
    rw [List.filterMap_some]
  · have sink_aft := congr_arg (sinkString lg.sinkNt) aft
    unfold sinkString at *
    rw [List.filterMap_append_append] at sink_aft 
    convert sink_aft
    rw [← preimage]
    unfold liftRule
    dsimp only
    unfold liftString
    rw [List.filterMap_map]
    rw [correct_inverse]
    rw [List.filterMap_some]

lemma sink_deri (lg : LiftedGrammar) (w₁ w₂ : List (Symbol T lg.g.nt))
    (hyp : CFDerives lg.g w₁ w₂) (ok_input : GoodString w₁) :
    CFDerives lg.g₀ (sinkString lg.sinkNt w₁) (sinkString lg.sinkNt w₂) ∧ GoodString w₂ :=
  by
  induction' hyp with x y trash orig ih
  · constructor
    · apply CF_deri_self
    · exact ok_input
  constructor
  · apply CF_deri_of_deri_tran
    · exact ih.left
    exact sink_tran orig ih.right
  · intro a in_y
    have ihr := ih.right a
    rcases orig with ⟨r, in_rules, u, y, bef, aft⟩
    rw [bef] at ihr 
    rw [List.mem_append] at ihr 
    rw [aft] at in_y 
    rw [List.mem_append] at in_y 
    cases in_y
    rw [List.mem_append] at in_y 
    cases in_y
    · apply ihr
      rw [List.mem_append]
      left
      left
      exact in_y
    · have exn₀ : ∃ n₀ : lg.g₀.nt, lg.liftNt n₀ = r.fst :=
        by
        by_cases lg.sinkNt r.fst = none
        · exfalso
          have ruu : Symbol.nonterminal r.fst ∈ x :=
            by
            rw [bef]
            rw [List.mem_append]
            left
            rw [List.mem_append]
            right
            apply List.mem_cons_self
          have glruf : GoodLetter (Symbol.nonterminal r.fst) :=
            ih.right (Symbol.nonterminal r.fst) ruu
          unfold GoodLetter at glruf 
          rw [h] at glruf 
          cases' glruf with n₀ imposs
          exact Option.noConfusion imposs
        cases' option.ne_none_iff_exists'.mp h with x ex
        use x
        have gix := lifted_grammar_inverse lg r.fst ⟨x, ex⟩
        rw [ex] at gix 
        rw [Option.map_some'] at gix 
        apply Option.some_injective
        exact gix
      rcases lg.preimage_of_rules r ⟨in_rules, exn₀⟩ with ⟨r₀, in0, lif⟩
      rw [← lif] at in_y 
      unfold liftRule at in_y 
      dsimp only at in_y 
      unfold liftString at in_y 
      rw [List.mem_map] at in_y 
      rcases in_y with ⟨s, s_in_rulsnd, symbol_letter⟩
      rw [← symbol_letter]
      cases s
      · unfold liftSymbol
      unfold liftSymbol
      unfold GoodLetter
      use s
      exact lg.lift_nt_sink s
    · apply ihr
      right
      exact in_y

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
unsafe def five_steps : tactic Unit :=
  sorry

variable {g₁ g₂ : CFGrammar T}

/-- similar to `lift_symbol (option.some ∘ sum.inl)` -/
def sTNOfSTN₁ : Symbol T g₁.nt → Symbol T (Option (Sum g₁.nt g₂.nt))
  | Symbol.terminal st => Symbol.terminal st
  | Symbol.nonterminal snt => Symbol.nonterminal (some (Sum.inl snt))

/-- similar to `lift_symbol (option.some ∘ sum.inr)` -/
def sTNOfSTN₂ : Symbol T g₂.nt → Symbol T (Option (Sum g₁.nt g₂.nt))
  | Symbol.terminal st => Symbol.terminal st
  | Symbol.nonterminal snt => Symbol.nonterminal (some (Sum.inr snt))

/-- similar to `lift_string (option.some ∘ sum.inl)` -/
def lsTNOfLsTN₁ : List (Symbol T g₁.nt) → List (Symbol T (Option (Sum g₁.nt g₂.nt))) :=
  List.map sTNOfSTN₁

/-- similar to `lift_string (option.some ∘ sum.inr)` -/
def lsTNOfLsTN₂ : List (Symbol T g₂.nt) → List (Symbol T (Option (Sum g₁.nt g₂.nt))) :=
  List.map sTNOfSTN₂

/-- similar to `lift_rule (option.some ∘ sum.inl)` -/
def ruleOfRule₁ (r : g₁.nt × List (Symbol T g₁.nt)) :
    Option (Sum g₁.nt g₂.nt) × List (Symbol T (Option (Sum g₁.nt g₂.nt))) :=
  (some (Sum.inl (Prod.fst r)), lsTNOfLsTN₁ (Prod.snd r))

/-- similar to `lift_rule (option.some ∘ sum.inr)` -/
def ruleOfRule₂ (r : g₂.nt × List (Symbol T g₂.nt)) :
    Option (Sum g₁.nt g₂.nt) × List (Symbol T (Option (Sum g₁.nt g₂.nt))) :=
  (some (Sum.inr (Prod.fst r)), lsTNOfLsTN₂ (Prod.snd r))

-/