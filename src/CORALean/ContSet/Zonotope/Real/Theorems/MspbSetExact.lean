module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A parallelotope plus a box is a zonotope with `2n` generators

[1, Prop. 4.2, Eqs. 17-20]: `A [r] ⊕ [v] = c ⊕ R B²ⁿ` with center `c = A mid([r]) + mid([v])` and
generators `R = [A dr([r]) | dr([v])]`, `dr(·) = diag(rad(·))`. The zonotope is
`(A □[r]) ⊕ □[v]` built from `Interval.zonotope`, whose center and generators are `mid` and
`diag(rad)`; exact for boxes with `inf ≤ sup`.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mspb_set_exact (A : Mat ℝ n n) (R V : Interval (Vec ℝ n))
    (hR : ∀ i, R.inf i ≤ R.sup i) (hV : ∀ i, V.inf i ≤ V.sup i) :
    {x | ∃ r ∈ R.construct, ∃ v ∈ V.construct, x = A *ᵥ r + v} =
      ((R.zonotope.map (Matrix.mulVecLin A)).plus V.zonotope).construct := by -- --- PROOF ---
  rw [← Zonotope.plus_exact, ← Zonotope.map_exact, ← Interval.zonotope_exact R hR,
    ← Interval.zonotope_exact V hV]
  ext x
  constructor
  · rintro ⟨r, hr, v, hv, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, v, hv, rfl⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, v, hv, rfl⟩
    exact ⟨r, hr, v, hv, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
