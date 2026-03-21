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

lemma CSG.language_eq_toGeneral_language (g : CSG T) :
    g.language = g.toGeneral.language :=
by
  unfold CSG.language Grammar.language
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    induction' h with x y _ hxy ih
    · apply gr_deri_self
    apply gr_deri_of_deri_tran ih
    rcases hxy with ⟨r, rin, u, v, bef, aft⟩
    use {
      inputL := r.contextL
      inputN := r.inputN
      inputR := r.contextR
      output := r.contextL ++ r.output ++ r.contextR
    }
    constructor
    · apply List.mem_map_of_mem; exact rin
    use u, v
    rw [bef, aft]
    constructor <;> rfl
  · intro h
    induction' h with x y _ hxy ih
    · apply cs_deri_self
    apply cs_deri_of_deri_tran ih
    rcases hxy with ⟨r_gen, r_gen_in, u, v, bef, aft⟩
    rw [List.mem_map] at r_gen_in
    rcases r_gen_in with ⟨r, rin, r_def⟩
    use r, rin, u, v
    rw [←r_def] at bef aft
    constructor
    · exact bef
    · exact aft

/-- Predicate "is context-sensitive" implies "is grammar-generated" (Type 0). -/
theorem IsCS_implies_IsGG {L : Language T} :
    L.IsCS → L.IsGG :=
by
  rintro ⟨g, hg⟩
  use g.toGeneral
  rw [←hg, CSG.language_eq_toGeneral_language]
