import Chomsky.Classes.ContextSensitive.Basics.Toolbox
import Chomsky.Classes.Unrestricted.Basics.Toolbox
import Mathlib.Tactic

variable {T : Type}


/-- Convert a context-sensitive grammar to an unrestricted grammar. -/
def CSG.toGeneral (g : CSG T) : Grammar T where
  nt := g.nt
  initial := g.initial
  rules := g.rules.map fun r => {
    inputL := r.contextL
    inputN := r.inputN
    inputR := r.contextR
    output := r.contextL ++ r.output ++ r.contextR
  }

private lemma CSG.tran_iff_toGeneral_tran (g : CSG T) (w₁ w₂ : List (Symbol T g.nt)) :
    g.Transforms w₁ w₂ ↔ g.toGeneral.Transforms w₁ w₂ :=
by
  constructor <;> intro ⟨r, rin, u, v, bef, aft⟩
  · use { inputL := r.contextL, inputN := r.inputN, inputR := r.contextR, output := r.contextL ++ r.output ++ r.contextR },
      (by apply List.mem_map_of_mem; exact rin), u, v, bef, aft
  · rw [List.mem_map] at rin
    rcases rin with ⟨r₀, rin₀, r_def⟩
    use r₀, rin₀, u, v
    rw [←r_def] at bef aft
    exact ⟨bef, aft⟩

private lemma CSG.deri_iff_toGeneral_deri (g : CSG T) (w₁ w₂ : List (Symbol T g.nt)) :
    g.Derives w₁ w₂ ↔ g.toGeneral.Derives w₁ w₂ :=
by
  constructor <;> intro h
  · induction' h with x y _ hxy ih
    · apply gr_deri_self
    · apply gr_deri_of_deri_tran ih
      rwa [←CSG.tran_iff_toGeneral_tran]
  · induction' h with x y _ hxy ih
    · apply cs_deri_self
    · apply cs_deri_of_deri_tran ih
      rwa [CSG.tran_iff_toGeneral_tran]

lemma CSG.language_eq_toGeneral_language (g : CSG T) :
    g.language = g.toGeneral.language :=
by
  unfold CSG.language Grammar.language
  ext w
  simp only [Set.mem_setOf_eq]
  apply CSG.deri_iff_toGeneral_deri

/-- Predicate "is context-sensitive" implies "is grammar-generated" (Type 0). -/
theorem IsCS_implies_IsGG {L : Language T} :
    L.IsCS → L.IsGG :=
by
  rintro ⟨g, hg⟩
  use g.toGeneral
  rw [←hg, CSG.language_eq_toGeneral_language]
