/-import Project.Classes.ContextFree.ClosureProperties.Bijection

/-- The class of context-free languages is closed under permutation of terminals. -/
lemma CF_of_permute_CF {T : Type} (π : Equiv.Perm T) (L : Language T) :
    IsCF L → IsCF (permuteLang L π) :=
  CF_of_bijemap_CF π L
-/
