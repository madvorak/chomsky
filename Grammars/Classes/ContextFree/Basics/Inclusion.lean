import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Classes.ContextSensitive.Basics.Inclusion

variable {T : Type}


private def CFgrammar.discardEmpty (g : CFgrammar T) (n : g.nt) (n_to_nil_in_gr : (n, []) ∈ g.rules) : CFgrammar T :=
  g -- TODO remove `(n, [])` from `g.rules` and then, for every rule containing `n` on the right-hand side, duplicate

private def CFgrammar.hasEmptyRule (g : CFgrammar T) : Option g.nt :=
  none -- TODO test if any `(n, [])` is in `g.rules`

private partial def CFgrammar.eliminateEmptyRules (g : CFgrammar T) : CFgrammar T :=
  match g.hasEmptyRule with
  | none   => g -- TODO prove termination
  | some n => (g.discardEmpty n sorry).eliminateEmptyRules

private lemma CFgrammar.discardEmpty_preserves_language {g : CFgrammar T} {n : g.nt} (ass : (n, []) ∈ g.rules) :
  (g.discardEmpty n ass).language = g.language  :=
by -- TODO allow `(g.discardEmpty n ass).language` and `g.language` to differ in `[] ∈ g.language` when `n = g.initial`
  sorry

private lemma CFgrammar.eliminateEmptyRules_preserves_language (g : CFgrammar T) :
  g.eliminateEmptyRules.language = g.language  :=
by -- TODO allow `(g.discardEmpty n ass).language` and `g.language` to differ in `[] ∈ g.language`
  sorry

def csg_of_cfg (g : CFgrammar T) : CSgrammar T :=
  sorry

def grammar_of_cfg (g : CFgrammar T) : Grammar T :=
  Grammar.mk g.nt g.initial (
    List.map (fun r : g.nt × List (Symbol T g.nt) => Grule.mk [] r.fst [] r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CFgrammar T) :
  grammar_of_csg (csg_of_cfg g) = grammar_of_cfg g :=
by
  sorry

lemma grammar_of_csg_of_cfg :
  grammar_of_csg ∘ csg_of_cfg = @grammar_of_cfg T :=
by
  ext
  apply grammar_of_cfg_well_defined

lemma cfLanguage_eq_csLanguage (g : CFgrammar T) :
  g.language = (csg_of_cfg g).language :=
by
  sorry

lemma cfLanguage_eq_grammarLanguage (g : CFgrammar T) :
  g.language = (grammar_of_cfg g).language :=
by
  rw [← grammar_of_cfg_well_defined]
  rw [cfLanguage_eq_csLanguage]
  rw [csLanguage_eq_grammarLanguage]

theorem CF_subclass_CS {L : Language T} :
  IsCF L → IsCS L :=
by
  rintro ⟨g, eq_L⟩
  use csg_of_cfg g
  rw [← eq_L]
  rw [cfLanguage_eq_csLanguage]

theorem CF_subclass_RE {L : Language T} :
  IsCF L → IsGG L :=
CS_subclass_RE ∘ CF_subclass_CS
