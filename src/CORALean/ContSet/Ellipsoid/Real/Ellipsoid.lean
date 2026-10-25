module

public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# Ellipsoids: the representation

The definition is [1, Def. 4], CORA's `ellipsoid(Q, q)`: a shape matrix `Q` and a center `q`,
denoting `{x | (x - q)ᵀ Q⁺ (x - q) ≤ 1, x - q ∈ range Q}`. The paper prints `Q⁻¹`; the
pseudo-inverse `Q⁺` is what a semi-definite `Q` needs and what CORA computes, and is `Q⁻¹` when `Q`
is invertible (`Theorems/IsPinvQpinv`). That `Q` is positive semi-definite is a field, as CORA's
constructor refuses any other. The square root `G = Q^(1/2)` (`CFC.sqrt`, CORA's `sqrtm`;
`Operations/Basic.lean`) is a derived helper: the set is `{q + G u | ‖u‖₂ ≤ 1}`
(`Theorems/ConstructEqSqrt`), and any `F` with `F Fᵀ = Q` gives the same set
(`Theorems/ConstructEqOfFactor`). `‖·‖₂` is `CORALean.norm₂`; `Vec ℝ n` carries the sup norm.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- An ellipsoid with positive semidefinite shape matrix `Q` and center `q`. -/
structure Ellipsoid (n : ℕ) where
  /-- The shape matrix. -/
  Q : Mat ℝ n n
  /-- The center. -/
  q : Vec ℝ n
  /-- CORA's constructor checks this, up to its tolerance `TOL`. -/
  psd : Q.PosSemidef

/-- `Q⁺`, the Moore-Penrose pseudo-inverse of the shape matrix: the inverse of each eigenvalue,
`0` staying `0`, so `Q⁻¹` where `Q` is invertible. -/
noncomputable def Ellipsoid.Qpinv (E : Ellipsoid n) : Mat ℝ n n := cfc (fun x : ℝ => x⁻¹) E.Q

/-- [1, Def. 4]: `{x | (x - q)ᵀ Q⁺ (x - q) ≤ 1}`, with `x - q` in the range of `Q`, which a
degenerate `Q` confines it to. -/
def Ellipsoid.construct (E : Ellipsoid n) : Set (Vec ℝ n) :=
  {x | (x - E.q) ⬝ᵥ E.Qpinv *ᵥ (x - E.q) ≤ 1 ∧ ∃ w : Vec ℝ n, x - E.q = E.Q *ᵥ w}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
