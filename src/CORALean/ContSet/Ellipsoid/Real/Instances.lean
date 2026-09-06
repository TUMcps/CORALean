import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter

/-!
# What `Ellipsoid` instantiates

`ContSet` and `Mtimes` by instance search, and `Plus` only once a caller has
named the parameter it carries. An ellipsoid is closed under a linear image and
under nothing else the interface names: a Minkowski sum of two ellipsoids is not
an ellipsoid, a `linComb` of two is not one either, and `reduce` would be a
fitting problem rather than a ranking.

`Ellipsoid.plus_outer` holds at a fixed `l` for every pair of ellipsoids, so
fixing `l` — with the proof that it is positive — yields a lawful `Plus`. It is
a `def` and not an `instance` on purpose: instance search must not make a
precision choice, so the caller writes `letI := Ellipsoid.plusInstance hl`. One
instance then fixes `l` for a whole run, where the tightest depends on the
operands and the direction; a caller wanting it per call names `Ellipsoid.plus`.

At `Vec ℝ n` only: an ellipsoid is described by a Euclidean norm, which a
general real module has none of. No family notation is missing — `Ellipsoid` is
already indexed by the dimension, so a use site writes `(S := Ellipsoid)`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (Ellipsoid n) (Vec ℝ n) := ⟨Ellipsoid.construct⟩

/-- `Plus` at a scaling the caller chooses. Deliberately not an `instance`:
picking `l` is a precision decision and instance search may not make one. -/
@[reducible] noncomputable def Ellipsoid.plusInstance {l : ℝ} (hl : 0 < l) :
    ∀ n, Plus (Ellipsoid n) (Vec ℝ n) := fun _ =>
  { plus := Ellipsoid.plus l
    plus_outer := Ellipsoid.plus_outer l hl }

instance : Mtimes (Mat ℝ) (fun n => Ellipsoid n) where
  mtimes := Ellipsoid.mtimes
  mtimes_outer M E := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Ellipsoid.mtimes_exact M E).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
