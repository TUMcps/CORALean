import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter

/-!
# What `Ellipsoid` instantiates

`ContSet` and `Mtimes` by instance search, and `Plus` only once a caller has
named the parameter it carries. An ellipsoid is closed under a linear image and
nothing else the interface names: a Minkowski sum of two ellipsoids is not one,
nor is a `linComb`, and `reduce` would be a fitting problem, not a ranking.

`Ellipsoid.plus_outer` holds at a fixed pair of scalings for every pair of
ellipsoids, so fixing `s₁` and `s₂` — with the inequality they owe — yields a
lawful `Plus`. It is a `def` and not an `instance` on purpose: instance search
must not make a precision choice, so a caller writes
`letI := Ellipsoid.plusInstance hne₁ hne₂ hs`. One instance then fixes the pair
for a whole run, where the tightest depends on the operands and the direction;
a caller wanting it per call names `Ellipsoid.plus`.

At `Vec ℝ n` only: an ellipsoid is described by a Euclidean norm, which a
general real module has none of. No family notation is missing — `Ellipsoid` is
already indexed by the dimension, so a use site writes `(S := Ellipsoid)`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (Ellipsoid n) (Vec ℝ n) := ⟨Ellipsoid.construct⟩

/-- `Plus` at two scalings the caller chooses, with the inequality that makes
them sound. Deliberately not an `instance`: picking the pair is a precision
decision and instance search may not make one. -/
@[reducible] noncomputable def Ellipsoid.plusInstance {s₁ s₂ : ℝ} (hne₁ : s₁ ≠ 0)
    (hne₂ : s₂ ≠ 0) (hs : 1 / s₁ ^ 2 + 1 / s₂ ^ 2 ≤ 1) :
    ∀ n, Plus (Ellipsoid n) (Vec ℝ n) := fun _ =>
  { plus := Ellipsoid.plus s₁ s₂
    plus_outer := fun E₁ E₂ => Ellipsoid.plus_outer s₁ s₂ E₁ E₂ hne₁ hne₂ hs }

instance : Mtimes (Mat ℝ) (fun n => Ellipsoid n) where
  mtimes := Ellipsoid.mtimes
  mtimes_outer M E := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Ellipsoid.mtimes_exact M E).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
