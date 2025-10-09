import Chomsky.Classes.ContextFree.Basics.Toolbox
import Chomsky.Utilities.ListUtils

variable {T : Type}


/-- Lifting `Symbol` to a larger nonterminal type. -/
def liftSymbol {N₀ N : Type} (liftN : N₀ → N) : Symbol T N₀ → Symbol T N
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (liftN n)

/-- Sinking `Symbol` from a larger nonterminal type; may return `none`. -/
def sinkSymbol {N₀ N : Type} (sinkN : N → Option N₀) : Symbol T N → Option (Symbol T N₀)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal n => Option.map Symbol.nonterminal (sinkN n)

/-- Lifting `List Symbol` to a larger nonterminal type. -/
def liftString {N₀ N : Type} (liftN : N₀ → N) :
    List (Symbol T N₀) → List (Symbol T N) :=
  List.map (liftSymbol liftN)

/-- Sinking `List Symbol` from a larger nonterminal type; may skip some elements. -/
def sinkString {N₀ N : Type} (sinkN : N → Option N₀) :
    List (Symbol T N) → List (Symbol T N₀) :=
  List.filterMap (sinkSymbol sinkN)

/-- Lifting context-free rules to a larger nonterminal type. -/
def liftRule {N₀ N : Type} (liftN : N₀ → N) (r : N₀ × List (Symbol T N₀)) :
    N × List (Symbol T N) :=
  ⟨liftN r.fst, liftString liftN r.snd⟩

/-- Lifting `CFgrammar` to a larger nonterminal type. -/
structure LiftedCFG (T : Type) where
  /-- The smaller grammar. -/
  g₀: CFgrammar T
  /-- The bigger grammar. -/
  g : CFgrammar T
  /-- Mapping nonterminals from the smaller type to the bigger type. -/
  liftNT : g₀.nt → g.nt
  /-- Mapping nonterminals from the bigger type to the smaller type. -/
  sinkNT : g.nt → Option g₀.nt
  /-- The former map is injective. -/
  lift_inj : Function.Injective liftNT
  /-- The latter map is injective where defined. -/
  sink_inj : ∀ x y, sinkNT x = sinkNT y → x = y ∨ sinkNT x = none
  /-- The two mappings are essentially inverses. -/
  sinkNT_liftNT : ∀ n₀ : g₀.nt, sinkNT (liftNT n₀) = some n₀
  /-- Each rule of the smaller grammar has a corresponding rule in the bigger grammar. -/
  corresponding_rules : ∀ r : g₀.nt × List (Symbol T g₀.nt), r ∈ g₀.rules → liftRule liftNT r ∈ g.rules
  /-- Each rule of the bigger grammar whose input nonterminal the smaller grammar recognizes
      has a corresponding rule in the smaller grammar. -/
  preimage_of_rules :
    ∀ r : g.nt × List (Symbol T g.nt),
      (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, liftNT n₀ = r.fst) →
        (∃ r₀ ∈ g₀.rules, liftRule liftNT r₀ = r)

private lemma LiftedCFG.sinkNT_inverse_liftNT (G : LiftedCFG T) :
    ∀ x : G.g.nt, (∃ n₀, G.sinkNT x = some n₀) → (Option.map G.liftNT (G.sinkNT x) = x) := by
  intro x ⟨n₀, hx⟩
  rw [hx, Option.map_some']
  apply congr_arg
  by_contra hnx
  cases (G.sinkNT_liftNT n₀ ▸ G.sink_inj x (G.liftNT n₀)) hx with
  | inl case_valu => exact hnx case_valu.symm
  | inr case_none => exact Option.noConfusion (hx ▸ case_none)

private lemma LiftedCFG.lift_produces {G : LiftedCFG T}
    {w₁ w₂ : List (Symbol T G.g₀.nt)} (hG : G.g₀.Transforms w₁ w₂) :
    G.g.Transforms (liftString G.liftNT w₁) (liftString G.liftNT w₂) := by
  rcases hG with ⟨r, rin, hr⟩
  rcases hr with ⟨u, v, bef, aft⟩
  refine ⟨liftRule G.liftNT r, G.corresponding_rules r rin, ?_⟩
  use liftString G.liftNT u, liftString G.liftNT v
  constructor
  · simpa only [liftString, List.map_append] using congr_arg (liftString G.liftNT) bef
  · simpa only [liftString, List.map_append] using congr_arg (liftString G.liftNT) aft

/-- Derivation by `G.g₀` can be mirrored by `G.g` derivation. -/
lemma LiftedCFG.lift_derives {G : LiftedCFG T}
    {w₁ w₂ : List (Symbol T G.g₀.nt)} (hG : G.g₀.Derives w₁ w₂) :
    G.g.Derives (liftString G.liftNT w₁) (liftString G.liftNT w₂) := by
  induction hG with
  | refl => exact CFgrammar.deri_self
  | tail _ orig ih => exact CFgrammar.deri_of_deri_tran ih (lift_produces orig)

/-- A `Symbol` is good iff it is one of those nonterminals that result from sinking or it is any
terminal. -/
def LiftedCFG.GoodLetter {G : LiftedCFG T} : Symbol T G.g.nt → Prop
  | Symbol.terminal _ => True
  | Symbol.nonterminal n => ∃ n₀ : G.g₀.nt, G.sinkNT n = n₀

/-- A string is good iff every `Symbol` in it is good. -/
def LiftedCFG.GoodString {G : LiftedCFG T}
    (s : List (Symbol T G.g.nt)) : Prop :=
  ∀ a ∈ s, GoodLetter a

private lemma LiftedCFG.sink_produces {G : LiftedCFG T}
    {w₁ w₂ : List (Symbol T G.g.nt)} (hG : G.g.Transforms w₁ w₂) (hw₁ : GoodString w₁) :
    G.g₀.Transforms (sinkString G.sinkNT w₁) (sinkString G.sinkNT w₂) ∧
      GoodString w₂ := by
  rcases hG with ⟨r, rin, hr⟩
  rcases hr with ⟨u, v, bef, aft⟩
  rcases G.preimage_of_rules r (by
      refine ⟨rin, ?_⟩
      rw [bef] at hw₁
      obtain ⟨n₀, hn₀⟩ : GoodLetter (Symbol.nonterminal r.fst)
      · apply hw₁; simp
      use n₀
      simpa [G.sinkNT_inverse_liftNT r.fst ⟨n₀, hn₀⟩, Option.map_some'] using
        congr_arg (Option.map G.liftNT) hn₀.symm)
    with ⟨r₀, hr₀, hrr₀⟩
  constructor
  · use r₀
    refine ⟨hr₀, ?_⟩
    use sinkString G.sinkNT u, sinkString G.sinkNT v
    have correct_inverse : sinkSymbol G.sinkNT ∘ liftSymbol G.liftNT = Option.some
    · ext1 x
      cases x
      · rfl
      rw [Function.comp_apply]
      simp only [sinkSymbol, liftSymbol, Option.map_eq_some', Symbol.nonterminal.injEq]
      rw [exists_eq_right]
      apply G.sinkNT_liftNT
      exact T
    constructor
    · have middle :
        List.filterMap (sinkSymbol (T := T) G.sinkNT) [Symbol.nonterminal (G.liftNT r₀.fst)] =
          [Symbol.nonterminal r₀.fst]
      · simp [sinkSymbol, G.sinkNT_liftNT]
      simpa only [
        sinkString, List.filterMap_append, liftRule, ←hrr₀, middle
      ] using congr_arg (sinkString G.sinkNT) bef
    · simpa only [
        sinkString, List.filterMap_append, liftRule, liftString, List.filterMap_map, List.filterMap_some, ←hrr₀, correct_inverse
      ] using congr_arg (sinkString G.sinkNT) aft
  · rw [bef] at hw₁
    rw [aft, ← hrr₀]
    simp only [GoodString, List.forall_mem_append] at hw₁ ⊢
    refine ⟨⟨hw₁.left.left, ?_⟩, hw₁.right⟩
    intro a ha
    cases a
    · simp [GoodLetter]
    dsimp only [liftRule, liftString] at ha
    rw [List.mem_map] at ha
    rcases ha with ⟨s, -, hs⟩
    rw [← hs]
    cases s with
    | terminal _ => exact False.elim (Symbol.noConfusion hs)
    | nonterminal s' => exact ⟨s', G.sinkNT_liftNT s'⟩

private lemma LiftedCFG.sink_derives_aux {G : LiftedCFG T}
    {w₁ w₂ : List (Symbol T G.g.nt)} (hG : G.g.Derives w₁ w₂) (hw₁ : GoodString w₁) :
    G.g₀.Derives (sinkString G.sinkNT w₁) (sinkString G.sinkNT w₂) ∧
      GoodString w₂ := by
  induction hG with
  | refl => exact ⟨CFgrammar.deri_self, hw₁⟩
  | tail _ orig ih =>
    have both := sink_produces orig ih.right
    exact ⟨CFgrammar.deri_of_deri_tran ih.left both.left, both.right⟩

/-- Derivation by `G.g` can be mirrored by `G.g₀` derivation if that the starting word does not
contain any nonterminals that `G.g₀` lacks. -/
lemma LiftedCFG.sink_derives (G : LiftedCFG T)
    {w₁ w₂ : List (Symbol T G.g.nt)} (hG : G.g.Derives w₁ w₂) (hw₁ : GoodString w₁) :
    G.g₀.Derives (sinkString G.sinkNT w₁) (sinkString G.sinkNT w₂) :=
  (sink_derives_aux hG hw₁).left

lemma liftString_all_terminals {N₀ N : Type} (liftN : N₀ → N) (w : List T) :
    liftString liftN (w.map Symbol.terminal) = w.map Symbol.terminal := by
  induction w with
  | nil => rfl
  | cons t _ ih => exact congr_arg (Symbol.terminal t :: ·) ih

lemma sinkString_all_terminals {N₀ N : Type} (sinkN : N → Option N₀) (w : List T) :
    sinkString sinkN (w.map Symbol.terminal) = w.map Symbol.terminal := by
  induction w with
  | nil => rfl
  | cons t _ ih => exact congr_arg (Symbol.terminal t :: ·) ih

lemma singletonGoodString {G : LiftedCFG T}
    {s : Symbol T G.g.nt} (hs : G.GoodLetter s) : G.GoodString [s] := by
  simpa [LiftedCFG.GoodString] using hs
