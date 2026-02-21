import Mathlib.Logic.Relation
import Linters


section notations

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr

/-- The "left" or "top" variant. -/
prefix:max "◩" => Sum.inl

/-- The "right" or "bottom" variant. -/
prefix:max "◪" => Sum.inr

end notations


section unexpanders

@[app_unexpander List.map]
def List.map_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `map) $f)
  | _ => throw ()

@[app_unexpander List.filterMap]
def List.filterMap_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `filterMap) $f)
  | _ => throw ()

@[app_unexpander List.take]
def List.take_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `take) $n)
  | _ => throw ()

@[app_unexpander List.drop]
def List.drop_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `drop) $n)
  | _ => throw ()

end unexpanders
