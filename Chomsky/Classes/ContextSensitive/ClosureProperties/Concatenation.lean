import Chomsky.Classes.ContextSensitive.Basics.Inclusion
import Chomsky.Classes.Unrestricted.ClosureProperties.Concatenation
import Chomsky.Basic

variable {T : Type}

open Sum


private def wrapCSR₁ {N₁ : Type} (N₂ : Type) (r : CSRule T N₁) :
    CSRule T (nnn T N₁ N₂) where
  contextL := r.contextL.map (wrapSymbol₁ N₂)
  inputN := ◩(some ◩r.inputN)
  contextR := r.contextR.map (wrapSymbol₁ N₂)
  output := r.output.map (wrapSymbol₁ N₂)

private def wrapCSR₂ (N₁ : Type) {N₂ : Type} (r : CSRule T N₂) :
    CSRule T (nnn T N₁ N₂) where
  contextL := r.contextL.map (wrapSymbol₂ N₁)
  inputN := ◩(some ◪r.inputN)
  contextR := r.contextR.map (wrapSymbol₂ N₁)
  output := r.output.map (wrapSymbol₂ N₂)

private def CSG.terminalsRules₁ (g : CSG T) (N₂ : Type) :
    List (CSRule T (nnn T g.nt N₂)) :=
  (allUsedTerminals g.toGeneral).map fun t => {
    contextL := []
    inputN := ◪◩t
    contextR := []
    output := [Symbol.terminal t]
  }

private def CSG.terminalsRules₂ (g : CSG T) (N₁ : Type) :
    List (CSRule T (nnn T N₁ g.nt)) :=
  (allUsedTerminals g.toGeneral).map fun t => {
    contextL := []
    inputN := ◪◪t
    contextR := []
    output := [Symbol.terminal t]
  }

private def bigCSG (g₁ g₂ : CSG T) : CSG T where
  nt := nnn T g₁.nt g₂.nt
  initial := ◩none
  rules := {
    contextL := []
    inputN := ◩none
    contextR := []
    output := [
      Symbol.nonterminal ◩(some ◩g₁.initial),
      Symbol.nonterminal ◩(some ◪g₂.initial)
    ]
  } :: (
    g₁.rules.map (wrapCSR₁ g₂.nt) ++
    g₂.rules.map (wrapCSR₂ g₁.nt) ++
    g₁.terminalsRules₁ g₂.nt ++
    g₂.terminalsRules₂ g₁.nt
  )

private lemma bigCSG_language_eq_bigGrammar_language (g₁ g₂ : CSG T) :
    (bigCSG g₁ g₂).language = (bigGrammar g₁.toGeneral g₂.toGeneral).language :=
by
  rw [CSG.language_eq_toGeneral_language]
  apply congr_arg
  dsimp [bigCSG, bigGrammar, CSG.toGeneral]
  congr 2
  simp only [List.map_append, List.map_map]
  congr 2
  · simp only [rulesForTerminals₁, CSG.terminalsRules₁, List.map_map]
    rfl
  · simp only [rulesForTerminals₂, CSG.terminalsRules₂, List.map_map]
    rfl

/-- The class of context-sensitive languages is closed under concatenation. -/
theorem CS_of_CS_c_CS (L₁ : Language T) (L₂ : Language T) :
    L₁.IsCS ∧ L₂.IsCS → (L₁ * L₂).IsCS :=
by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  rw [g₁.language_eq_toGeneral_language, g₂.language_eq_toGeneral_language]
  use bigCSG g₁ g₂
  rw [bigCSG_language_eq_bigGrammar_language]
  apply Set.eq_of_subset_of_subset
  · exact in_concatenated_of_in_big
  · exact in_big_of_in_concatenated
