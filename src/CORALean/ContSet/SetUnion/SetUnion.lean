import CORALean.ContSet.ContSet.ContSet

/-!
# `SetUnion`: the union of a list of representations

The finite union CORA has no fixed combinator for: a caller lists branches and
`SetUnion` denotes `⋃ s ∈ sets, construct s`, `∅` at the empty list, matching
`Set.iUnion` over an empty index.

Generic over the member representation `S`, not split into `Real/` and
`Float/`: the type stores nothing but a `List S`, so no arithmetic of its own
sits here for a scalar to model — a float member type already routes every
number through `S`. `Instances.lean` inherits computability the same way:
mapping and folding a `List` is a plain `def` whenever `S`'s own operation is.

Not a fixed-size `Fin k → S` as `ZonoBundle` uses for its intersection: a union
has no algebraic reason to fix its arity, and a caller building one from a
growing worklist only wants to append.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A finite union of representations of the same type: `⋃ s ∈ sets, construct s`,
which is `∅` when `sets = []`. -/
structure SetUnion (S : Type) where
  sets : List S

/-- What a `SetUnion` denotes: the union of what every member denotes. -/
def SetUnion.construct [ContSet S α] (u : SetUnion S) : Set α :=
  ⋃ s ∈ u.sets, ContSet.construct s

instance [ContSet S α] : ContSet (SetUnion S) α := ⟨SetUnion.construct⟩

/-- Unfolds membership to a witnessing branch, for every proof below. -/
theorem SetUnion.mem_construct [ContSet S α] {u : SetUnion S} {x : α} :
    x ∈ ContSet.construct u ↔ ∃ s ∈ u.sets, x ∈ ContSet.construct s := by
  show x ∈ SetUnion.construct u ↔ _
  simp [SetUnion.construct]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
