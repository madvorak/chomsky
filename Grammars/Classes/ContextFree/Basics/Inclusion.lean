import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Classes.ContextSensitive.Basics.Inclusion

variable {T : Type}


def csg_of_cfg (g : CFgrammar T) : CSgrammar T :=
  CSgrammar.mk g.nt g.initial (
    List.map (fun r : g.nt × List (Symbol T g.nt) => CSrule.mk [] r.fst [] r.snd) g.rules)

def grammar_of_cfg (g : CFgrammar T) : Grammar T :=
  Grammar.mk g.nt g.initial (
    List.map (fun r : g.nt × List (Symbol T g.nt) => Grule.mk [] r.fst [] r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CFgrammar T) :
  grammar_of_csg (csg_of_cfg g) = grammar_of_cfg g :=
by
  unfold grammar_of_cfg
  delta csg_of_cfg
  delta grammar_of_csg
  simp only [List.map_map, eq_self_iff_true, heq_iff_eq, true_and_iff]
  sorry /-
  ext1
  rw [List.get?_map, List.get?_map]
  apply congr_fun
  ext1
  cases x
  · rfl
  apply congr_arg Option.some
  simp [List.append_nil] -/

lemma grammarOfCsg_of_cfg :
  grammar_of_csg ∘ csg_of_cfg = @grammar_of_cfg T :=
by
  ext
  apply grammar_of_cfg_well_defined

lemma cfLanguage_eq_csLanguage (g : CFgrammar T) :
  g.Language = (csg_of_cfg g).Language :=
by
  unfold CFgrammar.Language
  unfold CSgrammar.Language
  ext1 w
  sorry /-
  show
    CFDerives g [Symbol.nonterminal g.initial] (List.map Symbol.terminal w) =
      CSDerives (csgOfCfg g) [Symbol.nonterminal (csgOfCfg g).initial] (List.map Symbol.terminal w)
  rw [eq_iff_iff]
  constructor
  · have indu :
      ∀ v : List (Symbol T g.nt),
        CFDerives g [Symbol.nonterminal g.initial] v →
          CSDerives (csgOfCfg g) [Symbol.nonterminal (csgOfCfg g).initial] v :=
      by
      clear w
      intro v h
      induction' h with x y trash hyp ih
      · apply CS_deri_self
      apply CS_deri_of_deri_tran
      · exact ih
      unfold CFTransforms at hyp 
      unfold CSTransforms
      delta csgOfCfg
      dsimp only
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩
      use Csrule.mk [] r.fst [] r.snd
      constructor
      · rw [List.mem_map]
        use r
        constructor
        · exact rin
        · rfl
      use u
      use w
      constructor <;>
        · dsimp only
          rw [List.append_nil]
          rw [List.append_nil]
          assumption
    exact indu (List.map Symbol.terminal w)
  · have indu :
      ∀ v : List (Symbol T g.nt),
        CSDerives (csgOfCfg g) [Symbol.nonterminal g.initial] v →
          CFDerives g [Symbol.nonterminal (csgOfCfg g).initial] v :=
      by
      clear w
      intro v h
      induction' h with x y trash hyp ih
      · apply CF_deri_self
      apply CF_deri_of_deri_tran
      · exact ih
      unfold CSTransforms at hyp 
      unfold CFTransforms
      delta csgOfCfg at hyp 
      dsimp only at hyp 
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩
      use (r.input_nonterminal, r.output_string)
      constructor
      use u
      use w
      have cl_empty : r.context_left = List.nil := by simp
      have cr_empty : r.context_right = List.nil := by simp
      rw [cl_empty, cr_empty] at *
      repeat' rw [List.append_nil] at *
      constructor <;> assumption
    exact indu (List.map Symbol.terminal w) -/

lemma cfLanguage_eq_grammarLanguage (g : CFgrammar T) :
  g.Language = (grammar_of_cfg g).Language :=
by
  rw [← grammar_of_cfg_well_defined]
  rw [cfLanguage_eq_csLanguage]
  rw [csLanguage_eq_grammarLanguage]

theorem CF_subclass_CS {L : Language T} :
  IsCF L  →  IsCS L  :=
by
  rintro ⟨g, eq_L⟩
  use csg_of_cfg g
  rw [← eq_L]
  rw [cfLanguage_eq_csLanguage]

theorem CF_subclass_RE {L : Language T} :
  IsCF L  →  IsGG L  :=
CS_subclass_RE ∘ CF_subclass_CS
