import Grammars.Classes.Unrestricted.Thue.Definition

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
def ruleAnih : Trule alphabet specials := ⟨[a, a, S, b, b], [a, S, b]⟩
def ruleEnde : Trule alphabet specials := ⟨[a, S, b], []⟩

def mysis : Tsys alphabet := ⟨specials, specials.S_, [ruleSkip, ruleAnih, ruleEnde]⟩

example : [alphabet.a_, alphabet.a_, alphabet.b_, alphabet.b_] ∈ mysis.language := by
  unfold Tsys.language
  show (∃ n, Tsys.Derives mysis [S, a, a, b, b] [] n)
  use 4
  have lastStep : mysis.Transforms [a, S, b] []
  · use ruleEnde
    constructor
    · simp [mysis]
    use [], []
    simp [ruleEnde]
  apply Tsys.Derives.tail _ _ _ _ _ lastStep
  have prevStep : mysis.Transforms [a, a, S, b, b] [a, S, b]
  · use ruleAnih
    constructor
    · simp [mysis]
    use [], []
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
