import CORALean.ContSet.Zonotope.Real.Operations.SortByLength
import CORALean.ContSet.Zonotope.Real.Theorems.ConstructCompPerm

/-!
# Sorting the generators leaves the zonotope unchanged

`sortByLength` permutes the generators ([1, Sec. III-B, Step 1)]), which changes no point of the
zonotope.

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sortByLength_construct (Z : Zonotope (Vec ℝ n)) :
    Z.sortByLength.construct = Z.construct :=
  Zonotope.construct_comp_perm Z _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
