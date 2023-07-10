import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Classes.ContextSensitive.Basics.Inclusion

variable {T : Type}


def csg_of_cfg (g : CFgrammar T) : CSgrammar T :=
  sorry

def grammar_of_cfg (g : CFgrammar T) : Grammar T :=
  Grammar.mk g.nt g.initial (
    List.map (fun r : g.nt × List (Symbol T g.nt) => Grule.mk [] r.fst [] r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CFgrammar T) :
  grammar_of_csg (csg_of_cfg g) = grammar_of_cfg g :=
by
  sorry

lemma grammarOfCsg_of_cfg :
  grammar_of_csg ∘ csg_of_cfg = @grammar_of_cfg T :=
by
  ext
  apply grammar_of_cfg_well_defined

lemma cfLanguage_eq_csLanguage (g : CFgrammar T) :
  g.Language = (csg_of_cfg g).Language :=
by
  sorry

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
