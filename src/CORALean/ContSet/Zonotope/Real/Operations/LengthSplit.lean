module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.Global.Partition
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `Zonotope.lengthSplit`

The split of [1, Sec. IV-D, Step 1)]: the `q` generators of largest 2-norm against the remaining
`ν - q`. Sorting is ascending, so the lengths enter negated.

## Inputs
* `Z` – zonotope
* `q` – kept count

## Hypotheses
* `hq` – at most all generators

## Output
* split into the `q` longest and the rest

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `q` longest generators (`part.left`) and the rest (`part.right`). -/
noncomputable def Zonotope.lengthSplit (Z : Zonotope (Vec ℝ n)) (q : ℕ) (hq : q ≤ Z.h) :
    Split (Fin Z.h) into (Fin q) ⊕ (Fin (Z.h - q)) :=
  (Partition.split q (Z.h - q)).reindex
    ((Tuple.sort fun j => -Z.generatorLength j).symm.trans
      (finCongr (Nat.add_sub_cancel' hq).symm))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
