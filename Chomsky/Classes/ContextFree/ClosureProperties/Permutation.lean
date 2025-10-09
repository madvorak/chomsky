/-import Project.Classes.ContextFree.ClosureProperties.Bijection

/-- The class of context-free languages is closed under permutation of terminals. -/
lemma CF_of_permute_CF {T : Type} (π : Equiv.Perm T) (L : Language T) :
    L.IsCF → (L.permute π).IsCF :=
  CF_of_bijemap_CF π L
-/
