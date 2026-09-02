import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact

/-!
# What `Ellipsoid` instantiates

`ContSet` and `Mtimes`, and deliberately nothing else. An ellipsoid is closed
under a linear image and under nothing else the interface names: a Minkowski sum
of two ellipsoids is not an ellipsoid, a `linComb` of two is not one either, and
`reduce` would be a fitting problem rather than a ranking. Each of those admits
an outer approximation, but every one of them carries a free parameter, and a
class field with no room for it would be a precision choice hidden in an
interface. `Operations.Plus` states the family and leaves the choice to the
caller.

At `Vec ℝ n` only: an ellipsoid is described by a Euclidean norm, which a
general real module has none of.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

instance : ContSet (Ellipsoid n) (Vec ℝ n) := ⟨Ellipsoid.construct⟩

instance : Mtimes (Mat ℝ) (fun n => Ellipsoid n) where
  mtimes := Ellipsoid.mtimes
  mtimes_outer M E := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Ellipsoid.mtimes_exact M E).subset

end CORALean.Real
