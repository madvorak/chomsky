import Grammars.Classes.Unrestricted.Thue.Definition
import Grammars.Utilities.ListUtils

inductive alphabet
  | a_ : alphabet
  | b_ : alphabet

inductive specials
  | S_ : specials

def Symb : Type := Tsymb alphabet specials

def a : Symb := Tsymb.letter alphabet.a_
def b : Symb := Tsymb.letter alphabet.b_
def S : Symb := Tsymb.marker specials.S_

def ruleSkip : Trule alphabet specials := ⟨[S, a], [a, S]⟩
def ruleAnih : Trule alphabet specials := ⟨[a, S, b], [S]⟩

def mysis : Tsys alphabet := ⟨specials, specials.S_, [ruleSkip, ruleAnih]⟩

example : [alphabet.a_, alphabet.a_, alphabet.b_, alphabet.b_] ∈ mysis.language := by
  unfold Tsys.language
  show (∃ n, Tsys.Derives mysis [S, a, a, b, b] [S] n)
  use 4
  have lastStep : mysis.Transforms [a, S, b] [S]
  · use ruleAnih
    constructor
    · simp [mysis]
    use [], []
    simp [ruleAnih]
  apply Tsys.Derives.tail _ _ _ _ _ lastStep
  have prevStep : mysis.Transforms [a, a, S, b, b] [a, S, b]
  · use ruleAnih
    constructor
    · simp [mysis]
    use [a], [b]
    simp [ruleAnih]
  apply Tsys.Derives.tail _ _ _ _ _ prevStep
  have sndStep : mysis.Transforms [a, S, a, b, b] [a, a, S, b, b]
  · use ruleSkip
    constructor
    · simp [mysis]
    use [a], [b, b]
    simp [ruleSkip]
  apply Tsys.Derives.tail _ _ _ _ _ sndStep
  have fstStep : mysis.Transforms [S, a, a, b, b] [a, S, a, b, b]
  · use ruleSkip
    constructor
    · simp [mysis]
    use [], [a, b, b]
    simp [ruleSkip]
  apply Tsys.Derives.tail _ _ _ _ _ fstStep
  apply Tsys.Derives.refl

example : mysis.IsDeterministic := by
  classical
  intro w s n derived x y hyp
  have at_most_one_marker : s.countIn S ≤ 1
  · induction' derived
    · simp [mysis, Tsys.initiate, S]
      --rw [List.countIn_cons]
      sorry
    · sorry
  -- applications of `ruleSkip` and `ruleAnih` are mutually exclusible
  rcases hyp with ⟨⟨rₓ, rinₓ, u, v, bef, aft⟩, ⟨rₐ, rest⟩⟩
  sorry
