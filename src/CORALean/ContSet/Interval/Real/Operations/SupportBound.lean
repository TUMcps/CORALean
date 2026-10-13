import CORALean.ContSet.Interval.Real.Operations.SupportBoundEntrywise

/-!
# A box answers a direction corner by corner, at `Vec ℝ n`

A one-line specialisation of `Interval.supportBoundEntrywise`: `Vec ℝ n`'s
`Entrywise` instance is the identity on both `entry` and `ofEntry`, so
`ofEntry (Pi.single i 1)` reduces to `Pi.single i 1` by `rfl` and the general
`val`/`le` match this type's exactly — checked, not assumed. Kept under its own
name because `Zonotope_to_HPolytope` and others may already name it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No linear program: the value is a sum of corner products, one per
coordinate, each attained by moving that coordinate to its far endpoint. -/
noncomputable def Interval.supportBound (I : Interval (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound I.construct c :=
  Interval.supportBoundEntrywise I c

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
