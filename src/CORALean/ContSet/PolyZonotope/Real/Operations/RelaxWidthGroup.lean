import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.Global.Partition

/-!
# `ξ_E` from one grouped generator to the target it is merged onto

`relaxWidthMulti`'s width read between the two columns a *group* merge relates:
a member of the group on the right of the partition, and the target on the
left. One width per member rather than one per merge, since a group merge pays
each member separately.

Beside `relaxExpGroup` as `relaxWidthMulti` sits beside `relaxExpMulti`: read
again by `Theorems/RelaxExpGroupOuter.lean` and by the comparison with the
pairwise merges, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E` summed over every factor, from grouped generator `l` to the target
`t` it is merged onto. -/
def PolyZonotope.relaxWidthGroup (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin k)) (t : Fin d) (l : Fin k) : ℕ :=
  ∑ i, PolyZonotope.eDiff (pZ.E i (part.right l)) (pZ.E i (part.left t))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
