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
  constructor
  · rintro ⟨r, rin, u, v, bef, aft⟩
    refine ⟨{ inputL := r.contextL, inputN := r.inputN, inputR := r.contextR, output := r.contextL ++ r.output ++ r.contextR }, ?_, u, v, bef, ?_⟩
    · dsimp [CSG.toGeneral]; apply List.mem_map_of_mem; exact rin
    · rw [aft]; simp only [List.append_assoc]
  · rintro ⟨r, rin, u, v, bef, aft⟩
    dsimp [CSG.toGeneral] at rin; rw [List.mem_map] at rin
    rcases rin with ⟨r₀, rin₀, r_def⟩
    use r₀, rin₀, u, v
    rw [←r_def] at bef aft
    dsimp at bef aft
    constructor
    · exact bef
    · rw [aft]; simp only [List.append_assoc]

private lemma CSG.deri_iff_toGeneral_deri (g : CSG T) (w₁ w₂ : List (Symbol T g.nt)) :
    g.Derives w₁ w₂ ↔ g.toGeneral.Derives w₁ w₂ :=
by
  constructor <;> intro h
  · induction h with
    | refl => apply gr_deri_self
    | tail _ hxy ih =>
      apply gr_deri_of_deri_tran ih
      rwa [←CSG.tran_iff_toGeneral_tran]
  · induction h with
    | refl => apply cs_deri_self
    | tail _ hxy ih =>
      apply cs_deri_of_deri_tran ih
      rwa [CSG.tran_iff_toGeneral_tran]

lemma CSG.language_eq_toGeneral_language (g : CSG T) :
    g.language = g.toGeneral.language :=
by
  unfold CSG.language Grammar.language
  ext w
  dsimp only [Set.mem_setOf_eq]
  apply CSG.deri_iff_toGeneral_deri

/-- Predicate "is context-sensitive" implies "is grammar-generated" (Type 0). -/
theorem IsCS_implies_IsGG {L : Language T} :
    L.IsCS → L.IsGG :=
by
  rintro ⟨g, hg⟩
  use g.toGeneral
  rw [←hg, CSG.language_eq_toGeneral_language]
