module

public import CORALean.Specification.STL.Operations.DepReachAt
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The interval bloating is centred at the origin

`D₀ = 0` and `D` is centred at `0`, so `D_{i+1} = interval(e^{AΔt}D_i ⊕ D)` of [1, Prop. 1],
which keeps the centre, is at every `i`.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachAt_D_c (A : Mat ℝ n n) (Δt : ℝ) (cs : STL.DepReachConsts n)
    (X₀ : Zonotope (Vec ℝ n)) (hD : cs.D.c = 0) (i : ℕ) :
    (STL.depReachAt A Δt cs X₀ i).D.c = 0 := by -- --- PROOF ---
  induction i with
  | zero => rfl
  | succ i ih =>
    show exp (Δt • A) *ᵥ (STL.depReachAt A Δt cs X₀ i).D.c + cs.D.c = 0
    rw [ih, hD]; simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
