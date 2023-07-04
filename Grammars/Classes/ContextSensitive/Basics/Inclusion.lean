import Grammars.Classes.ContextSensitive.Basics.Toolbox
import Grammars.Classes.Unrestricted.Basics.Toolbox

variable {T : Type}


def grammar_of_csg (g : CSgrammar T) : Grammar T :=
  Grammar.mk g.nt g.initial
    (List.map
      (fun r : CSrule T g.nt =>
        Grule.mk r.contextLeft r.inputNonterminal r.contextRight
          (r.contextLeft ++ r.outputString ++ r.contextRight))
      g.rules)

lemma csLanguage_eq_grammarLanguage (g : CSgrammar T) :
  g.Language = (grammar_of_csg g).Language :=
by
  unfold CSgrammar.Language
  unfold Grammar.Language
  ext1 w
  rw [Set.mem_setOf_eq]
  constructor
  · have indu :
      ∀ v : List (Symbol T g.nt),
        g.Derives [Symbol.nonterminal g.initial] v →
          (grammar_of_csg g).Derives [Symbol.nonterminal (grammar_of_csg g).initial] v
    · clear w
      intro v h
      induction' h with x y _ hyp ih
      · apply Grammar.deri_self
      apply Grammar.deri_of_deri_tran
      · exact ih
      unfold CSgrammar.Transforms at hyp 
      unfold Grammar.Transforms
      dsimp only [grammar_of_csg]
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩
      use Grule.mk
          r.contextLeft r.inputNonterminal r.contextRight
          (r.contextLeft ++ r.outputString ++ r.contextRight)
      constructor
      · rw [List.mem_map]
        use r
        constructor
        · exact rin
        · rfl
      use u
      use w
      constructor
      · exact bef
      simpa [List.append_assoc] using aft
    exact indu (List.map Symbol.terminal w)
  · have indu :
      ∀ v : List (Symbol T g.nt),
        (grammar_of_csg g).Derives [Symbol.nonterminal (grammar_of_csg g).initial] v →
          g.Derives [Symbol.nonterminal g.initial] v :=
      by
      clear w
      intro v h
      induction' h with x y _ hyp ih
      · apply CSgrammar.deri_self
      apply CSgrammar.deri_of_deri_tran
      · exact ih
      unfold Grammar.Transforms at hyp 
      unfold CSgrammar.Transforms
      dsimp only [grammar_of_csg] at hyp 
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩
      rw [List.mem_map] at rin 
      rcases rin with ⟨r', new_rule_in, new_rule_def⟩
      use r'
      constructor
      · exact new_rule_in
      use u
      use w
      constructor
      · rw [← new_rule_def] at bef 
        exact bef
      · rw [← new_rule_def] at aft 
        simpa [List.append_assoc] using aft
    exact indu (List.map Symbol.terminal w)

theorem CS_subclass_RE {L : Language T} :
  IsCS L  →  IsRE L  :=
by
  rintro ⟨g, eq_L⟩
  use grammar_of_csg g
  rw [← eq_L]
  rw [csLanguage_eq_grammarLanguage]
