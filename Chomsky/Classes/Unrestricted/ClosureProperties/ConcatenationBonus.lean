/-import Chomsky.Classes.ContextFree.Basics.Inclusion
import Chomsky.Classes.Unrestricted.ClosureProperties.Concatenation
import Chomsky.Utilities.WrittenByOthers.TrimAssoc

variable {T : Type}

private def wrap_CF_rule₁ {N₁ : Type} (N₂ : Type) (r : N₁ × List (Symbol T N₁)) :
    Nnn T N₁ N₂ × List (Nst T N₁ N₂) :=
  ◩(some ◩r.fst)), List.map (wrapSymbol₁ N₂) r.snd)

private def wrap_CF_rule₂ {N₂ : Type} (N₁ : Type) (r : N₂ × List (Symbol T N₂)) :
    Nnn T N₁ N₂ × List (Nst T N₁ N₂) :=
  ◩(some ◪r.fst)), List.map (wrapSymbol₂ N₁) r.snd)

private def CF_rules_for_terminals₁ (N₂ : Type) (g : CFG T) :
    List (Nnn T g.nt N₂ × List (Nst T g.nt N₂)) :=
  List.map (fun t => ◪◩t), [Symbol.terminal t])) (allUsedTerminals (grammarOfCfg g))

private def CF_rules_for_terminals₂ (N₁ : Type) (g : CFG T) :
    List (Nnn T N₁ g.nt × List (Nst T N₁ g.nt)) :=
  List.map (fun t => ◪◪t), [Symbol.terminal t])) (allUsedTerminals (grammarOfCfg g))

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def big_CF_grammar (g₁ g₂ : CFG T) : CFG T :=
  CFG.mk (Nnn T g₁.nt g₂.nt) ◩none)
    (◩none,
        [Symbol.nonterminal ◩(some ◩g₁.initial))),
          Symbol.nonterminal
            (Sum.inl
              (some
                (Sum.inr
                  g₂.initial)))])::List.map (wrapCFRule₁ g₂.nt) g₁.rules ++
          List.map (wrapCFRule₂ g₁.nt) g₂.rules ++
        (cFRulesForTerminals₁ g₂.nt g₁ ++ cFRulesForTerminals₂ g₁.nt g₂))

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[] -/
private lemma big_CF_grammar_same_language (g₁ g₂ : CFG T) :
    cFLanguage (bigCFG g₁ g₂) =
      grammarLanguage (bigGrammar (grammarOfCfg g₁) (grammarOfCfg g₂)) :=
  by
  rw [cFLanguage_eq_grammarLanguage]
  congr
  unfold big_CF_grammar
  unfold grammarOfCfg
  unfold bigGrammar
  dsimp only [List.map]
  congr
  repeat rw [List.map_append]
  trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `trim #[]"
  · apply congr_arg₂
    · unfold rulesForTerminals₁
      unfold CF_rules_for_terminals₁
      finish
    · unfold rulesForTerminals₂
      unfold CF_rules_for_terminals₂
      finish

/-- The class of context-free languages is closed under concatenation.
    This lemma is proved by translation from general grammars.
    Compare to `classes.context_free.closure_properties.concatenation.lean` which uses
    a simpler and more effective construction (based on context-gree grammars only). -/
private lemma bonus_CF_of_CF_c_CF (L₁ : Language T) (L₂ : Language T) :
    L₁.IsCF ∧ L₂.IsCF → (L₁ * L₂).IsCF :=
  by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  rw [cFLanguage_eq_grammarLanguage g₁] at eq_L₁
  rw [cFLanguage_eq_grammarLanguage g₂] at eq_L₂
  use big_CF_grammar g₁ g₂
  rw [big_CF_grammar_same_language]
  apply Set.eq_of_subset_of_subset
  · intro w hyp
    rw [←eq_L₁]
    rw [←eq_L₂]
    exact in_concatenated_of_in_big hyp
  · intro w hyp
    rw [←eq_L₁] at hyp
    rw [←eq_L₂] at hyp
    exact in_big_of_in_concatenated hyp
-/
