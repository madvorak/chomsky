/-import Project.Classes.ContextSensitive.Basics.Inclusion
import Project.Classes.Unrestricted.ClosureProperties.Concatenation

variable {T : Type}

private def wrap_CS_rule₁ {N₁ : Type} (N₂ : Type) (r : Csrule T N₁) : Csrule T (Nnn T N₁ N₂) :=
  Csrule.mk (List.map (wrapSymbol₁ N₂) r.contextLeft) (Sum.inl (some (Sum.inl r.inputNonterminal)))
    (List.map (wrapSymbol₁ N₂) r.contextRight) (List.map (wrapSymbol₁ N₂) r.outputString)

private def wrap_CS_rule₂ {N₂ : Type} (N₁ : Type) (r : Csrule T N₂) : Csrule T (Nnn T N₁ N₂) :=
  Csrule.mk (List.map (wrapSymbol₂ N₁) r.contextLeft) (Sum.inl (some (Sum.inr r.inputNonterminal)))
    (List.map (wrapSymbol₂ N₁) r.contextRight) (List.map (wrapSymbol₂ N₁) r.outputString)

private def CS_rules_for_terminals₁ (N₂ : Type) (g : CSGrammar T) :
    List (Csrule T (Nnn T g.Nt N₂)) :=
  List.map (fun t => Csrule.mk [] (Sum.inr (Sum.inl t)) [] [Symbol.terminal t])
    (allUsedTerminals (grammarOfCsg g))

private def CS_rules_for_terminals₂ (N₁ : Type) (g : CSGrammar T) :
    List (Csrule T (Nnn T N₁ g.Nt)) :=
  List.map (fun t => Csrule.mk [] (Sum.inr (Sum.inr t)) [] [Symbol.terminal t])
    (allUsedTerminals (grammarOfCsg g))

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def big_CS_grammar (g₁ g₂ : CSGrammar T) : CSGrammar T :=
  CSGrammar.mk (Nnn T g₁.Nt g₂.Nt) (Sum.inl none)
    (Csrule.mk [] (Sum.inl none) []
        [Symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
          Symbol.nonterminal
            (Sum.inl
              (some
                (Sum.inr
                  g₂.initial)))]::List.map (wrapCSRule₁ g₂.Nt) g₁.rules ++
          List.map (wrapCSRule₂ g₁.Nt) g₂.rules ++
        (cSRulesForTerminals₁ g₂.Nt g₁ ++ cSRulesForTerminals₂ g₁.Nt g₂))

private lemma big_CS_grammar_same_language (g₁ g₂ : CSGrammar T) :
    cSLanguage (bigCSGrammar g₁ g₂) =
      grammarLanguage (bigGrammar (grammarOfCsg g₁) (grammarOfCsg g₂)) :=
  by
  rw [cSLanguage_eq_grammarLanguage]
  congr
  unfold big_CS_grammar
  unfold grammarOfCsg
  unfold bigGrammar
  dsimp only [List.map]
  congr
  repeat' rw [List.map_append]
  apply congr_arg₂
  ·
    apply congr_arg₂ <;>
      · rw [List.map_map]
        rw [List.map_map]
        apply congr_arg₂
        · ext
          cases x
          change _ = Grule.mk _ _ _ _
          finish
        rfl
  · apply congr_arg₂
    · unfold rulesForTerminals₁
      unfold CS_rules_for_terminals₁
      rw [List.map_map]
      unfold grammarOfCsg
      finish
    · unfold rulesForTerminals₂
      unfold CS_rules_for_terminals₂
      rw [List.map_map]
      unfold grammarOfCsg
      finish

private lemma bonus_CS_of_CS_c_CS (L₁ : Language T) (L₂ : Language T) :
    L₁.IsCS ∧ L₂.IsCS → (L₁ * L₂).IsCS :=
  by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  rw [cSLanguage_eq_grammarLanguage g₁] at eq_L₁
  rw [cSLanguage_eq_grammarLanguage g₂] at eq_L₂
  use big_CS_grammar g₁ g₂
  rw [big_CS_grammar_same_language]
  apply Set.eq_of_subset_of_subset
  · intro w hyp
    rw [← eq_L₁]
    rw [← eq_L₂]
    exact in_concatenated_of_in_big hyp
  · intro w hyp
    rw [← eq_L₁] at hyp
    rw [← eq_L₂] at hyp
    exact in_big_of_in_concatenated hyp
-/
