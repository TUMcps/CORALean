module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec
public import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaPoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# `ContSet/Ellipsoid/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==================================  `apply_eq_dotProduct`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- A functional applied is the dot product with its `dualVec` -/
theorem apply_eq_dotProduct (c : Vec ℝ n →ₗ[ℝ] ℝ) (x : Vec ℝ n) : c x = dualVec c ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ c x, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; exact mul_comm _ _

end CORALean.Real


-- ===================================  `Ellipsoid.pullback`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- The direction pulled back into generator space, which is what the support
value is the length of. -/
noncomputable def Ellipsoid.pullback (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) : Vec ℝ E.k :=
  E.Gᵀ *ᵥ dualVec c

end CORALean.Real


-- =================================  `Ellipsoid.apply_mulVec`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- A functional applied to a generator-space image is the dot product with its pullback -/
theorem Ellipsoid.apply_mulVec (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) (u : Vec ℝ E.k) :
    c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := by
  rw [apply_eq_dotProduct, dotProduct_mulVec, Ellipsoid.pullback, mulVec_transpose]

end CORALean.Real


-- ==============================  `Ellipsoid.representsa_origin`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `ellipsoid/representsa_` at `origin`.

CORA's `@ellipsoid/representsa_` at type `origin` with tolerance `0`: a point at `q = 0`. -/
def Ellipsoid.representsa_origin (E : Ellipsoid n) : Prop := E.q = 0 ∧ E.representsa_point

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
