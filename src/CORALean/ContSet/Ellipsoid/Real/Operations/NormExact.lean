module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-!
# `Ellipsoid.normExact`

CORA's `@ellipsoid/norm_.m` (type `2` only, and only for the center `q = 0`):
`lmax = max(eig(E.Q)); val = sqrt(lmax)`, the square root of the largest eigenvalue of
the shape matrix `Q` (Mathlib's `eigenvalues₀`, sorted in decreasing order, so the first
one). The other norm types and a non-zero center are errors in CORA (`CORA:noExactAlg`,
`CORA:notSupported`); CORA's `-Inf` for an empty ellipsoid does not arise, an `Ellipsoid` here
always holds its center. The dimension is positive, as the largest eigenvalue of a `0 × 0` matrix
is not defined.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `norm_(E, 2)`: `sqrt(max(eig(Q)))`. The center is not read, CORA requires it to be `0`. -/
noncomputable def Ellipsoid.normExact (E : Ellipsoid n) (hn : 1 ≤ n) : ℝ :=
  let hQ : E.Q.IsHermitian := E.psd.isHermitian
  let lmax := hQ.eigenvalues₀ ⟨0, by rw [Fintype.card_fin]; exact hn⟩
  let val := Real.sqrt lmax
  val

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
