module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

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

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
