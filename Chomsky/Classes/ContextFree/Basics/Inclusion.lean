import Chomsky.Classes.ContextFree.Basics.Toolbox
import Chomsky.Classes.ContextSensitive.Basics.Inclusion

variable {T : Type}


private def CFG.discardEmpty (g : CFG T) (n : g.nt) (n_to_nil_in_gr : (n, []) ∈ g.rules) : CFG T :=
  g -- TODO remove `(n, [])` from `g.rules` and then, for every rule containing `n` on the right-hand side, duplicate

private def CFG.hasEmptyRule (g : CFG T) : Option g.nt :=
  none -- TODO test if any `(n, [])` is in `g.rules`

private partial def CFG.eliminateEmptyRules (g : CFG T) : CFG T :=
  match g.hasEmptyRule with
  | none   => g -- TODO prove termination
  | some n => (g.discardEmpty n sorry).eliminateEmptyRules

private lemma CFG.discardEmpty_preserves_language {g : CFG T} {n : g.nt} (hng : (n, []) ∈ g.rules) :
  (g.discardEmpty n hng).language = g.language  :=
by -- TODO allow `(g.discardEmpty n hng).language` and `g.language` to differ in `[] ∈ g.language` when `n = g.initial`
  sorry

private lemma CFG.eliminateEmptyRules_preserves_language (g : CFG T) :
  g.eliminateEmptyRules.language = g.language  :=
by -- TODO allow `(g.discardEmpty n ass).language` and `g.language` to differ in `[] ∈ g.language`
  sorry

def csg_of_cfg (g : CFG T) : CSG T :=
  sorry

def grammar_of_cfg (g : CFG T) : Grammar T :=
  Grammar.mk g.nt g.initial (
    List.map (fun r : g.nt × List (Symbol T g.nt) => Grule.mk [] r.fst [] r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CFG T) :
  grammar_of_csg (csg_of_cfg g) = grammar_of_cfg g :=
by
  sorry

lemma grammar_of_csg_of_cfg :
  grammar_of_csg ∘ csg_of_cfg = @grammar_of_cfg T :=
by
  ext
  apply grammar_of_cfg_well_defined

lemma cfLanguage_eq_csLanguage (g : CFG T) :
  g.language = (csg_of_cfg g).language :=
by
  sorry

lemma cfLanguage_eq_grammarLanguage (g : CFG T) :
  g.language = (grammar_of_cfg g).language :=
by
  rw [← grammar_of_cfg_well_defined]
  rw [cfLanguage_eq_csLanguage]
  rw [csLanguage_eq_grammarLanguage]

theorem CF_subclass_CS {L : Language T} :
  L.IsCF → L.IsCS :=
by
  rintro ⟨g, eq_L⟩
  use csg_of_cfg g
  rw [← eq_L]
  rw [cfLanguage_eq_csLanguage]

theorem CF_subclass_RE {L : Language T} :
  L.IsCF → L.IsGG :=
CS_subclass_RE ∘ CF_subclass_CS
