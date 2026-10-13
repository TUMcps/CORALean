import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `Ellipsoid.radius`

CORA's `@ellipsoid/radius`, `r = sqrt(eigs(E.Q, i))`: the square roots of the `i` largest
eigenvalues of the shape matrix `Q = G Gᵀ`, the radii of the enclosing hyperball and the next
semi-axes, the `j`-th entry (from `0`) being the `j+1`-th largest. CORA's default `i = 1` is
the enclosing radius. The eigenvalues are Mathlib's `eigenvalues₀`, sorted in decreasing
order. CORA's `zeros(dim(E), 0)` for an empty ellipsoid does not arise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.radius (E : Ellipsoid n) (i : ℕ) (hi : i ≤ n) : Fin i → ℝ :=
  let hQ : E.shape.IsHermitian := by
    simpa [Ellipsoid.shape] using Matrix.isHermitian_mul_conjTranspose_self E.G
  fun j => Real.sqrt (hQ.eigenvalues₀ ⟨j, by rw [Fintype.card_fin]; exact lt_of_lt_of_le j.2 hi⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
