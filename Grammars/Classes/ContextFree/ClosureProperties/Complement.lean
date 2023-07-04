/-import Project.Classes.ContextFree.ClosureProperties.Union
import Project.Classes.ContextFree.ClosureProperties.Intersection

/-- The class of context-free languages isn't closed under complement. -/
theorem nnyCF_of_complement_CF : ¬∀ T : Type, ∀ L : Language T, IsCF L → IsCF (Lᶜ) :=
  by
  intro h
  have nny := nnyCF_of_CF_i_CF
  push_neg at nny 
  rcases nny with ⟨T, L₁, L₂, ⟨hL₁, hL₂⟩, hyp_neg⟩
  specialize h T
  have hu := CF_of_CF_u_CF (L₁ᶜ) (L₂ᶜ) ⟨h L₁ hL₁, h L₂ hL₂⟩
  have contra := h (L₁ᶜ + L₂ᶜ) hu
  apply hyp_neg
  -- golfed by Eric Wieser
  rwa [Language.add_def, Set.compl_union, compl_compl, compl_compl] at contra 
-/
