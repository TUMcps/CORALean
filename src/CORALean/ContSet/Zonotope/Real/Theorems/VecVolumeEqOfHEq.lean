module

public import CORALean.ContSet.Zonotope.Real.Theorems.VolumeEqSquare
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.Global.MatVec

@[expose] public section

/-!
# The volume of a matrix zonotope with `n * m` generators

CORA's `@matZonotope/volume` is `volume(zonotope(matZ))`, the vector zonotope of the stacked
entries, so `Zonotope.volume` at `Zonotope.vec` is its definition and the theorems of the vector
class apply to it. With exactly `n * m` generators the Lebesgue volume of the set of stacked members
is that number (`volume_eq_of_h_eq`); `volume_eq_of_rank_lt` is the other case, in
`VecVolumeEqZero`.
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

/-- With as many generators as entries, the volume of the stacked members is
`volume(zonotope(matZ))`. -/
theorem Zonotope.vec_volume_eq_of_h_eq (Z : Zonotope (Mat ℝ m n)) (hh : Z.h = n * m) :
    MeasureTheory.volume (matVecEquiv '' Z.construct) = Z.vec.volume := by
  rw [Zonotope.vec_construct]
  exact Zonotope.volume_eq_of_h_eq Z.vec hh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
