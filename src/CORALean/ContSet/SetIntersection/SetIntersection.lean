module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `SetIntersection`: the intersection of a list of representations

`ZonoBundle`'s idea generalized past one member type: a caller lists branches
and `SetIntersection` denotes `⋂ s ∈ sets, construct s`, `univ` at the empty
list, matching `Set.iInter` over an empty index — the intersection over no
constraint at all.

Generic over the member representation `S`, not split into `Real/` and
`Float/`, for the same reason as `SetUnion`: the type stores nothing but a
`List S`, so no arithmetic of its own sits here for a scalar to model, and a
plain `List.map` computes whenever the member's own operation does.

`List S`, not `Fin k → S` as `ZonoBundle`: the two denote the same thing at a
fixed arity, and `List` is what lets a caller append rather than reindex.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A finite intersection of representations of the same type:
`⋂ s ∈ sets, construct s`, which is `univ` when `sets = []`. -/
structure SetIntersection (S : Type) where
  sets : List S

/-- What a `SetIntersection` denotes: the intersection of what every member denotes. -/
def SetIntersection.construct [ContSet S α] (I : SetIntersection S) : Set α :=
  ⋂ s ∈ I.sets, ContSet.construct s

instance [ContSet S α] : ContSet (SetIntersection S) α := ⟨SetIntersection.construct⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
