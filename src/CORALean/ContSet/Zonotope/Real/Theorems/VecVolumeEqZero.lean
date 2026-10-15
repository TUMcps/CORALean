module

public import CORALean.ContSet.Zonotope.Real.Theorems.VolumeEqZero
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.Global.MatVec

@[expose] public section

/-!
# The volume of a matrix zonotope of rank below `n * m`

CORA's early return of `volume_` for a rank-deficient `zonotope(matZ)`: its generators span less
than the whole space of entries, so the stacked members are a null set and `Zonotope.volume` is `0`
(`volume_eq_of_rank_lt`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A rank-deficient matrix zonotope: the volume of the stacked members is
`volume(zonotope(matZ))`. -/
theorem Zonotope.vec_volume_eq_of_rank_lt (Z : Zonotope (Mat ℝ m n)) (hr : Z.vec.rank < n * m) :
    MeasureTheory.volume (matVecEquiv '' Z.construct) = Z.vec.volume := by
  rw [Zonotope.vec_construct]
  exact Zonotope.volume_eq_of_rank_lt Z.vec hr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
