import Chomsky.Classes.ContextFree.Basics.Toolbox

variable {T : Type}

def CFG.toGeneral (g : CFG T) : Grammar T :=
  Grammar.mk g.nt g.initial (g.rules.map (fun r : g.nt × List (Symbol T g.nt) => Grule.mk [] r.fst [] r.snd))

lemma CFG.language_eq_toGeneral_language (g : CFG T) :
  g.language = g.toGeneral.language :=
by
  rw [CFG.toGeneral]
  sorry

theorem CF_subclass_RE {L : Language T} :
  L.IsCF → L.IsGG :=
by
  rintro ⟨g, rfl⟩
  exact ⟨g.toGeneral, g.language_eq_toGeneral_language.symm⟩
