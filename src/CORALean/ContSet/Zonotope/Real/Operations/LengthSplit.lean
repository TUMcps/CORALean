import CORALean.ContSet.Zonotope.Real.Operations.GeneratorLength
import CORALean.Global.Partition
import Mathlib.Data.Fin.Tuple.Sort

/-!
# `Zonotope.lengthSplit`

The split of [1, Sec. IV-D, Step 1)]: the `q` generators of largest 2-norm against the remaining
`ν - q`. Sorting is ascending, so the lengths enter negated.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


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
