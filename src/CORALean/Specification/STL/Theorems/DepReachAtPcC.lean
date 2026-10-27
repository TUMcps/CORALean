module

public import CORALean.Specification.STL.Operations.DepReachAt
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The particular solution is centered at the origin

`P_c(t₀) = 0` and `U₀ = B(U ⊕ (-c_u))` is centered at `0`, so
`P_c(t_{i+1}) = e^{AΔt}P_c(t_i) ⊕ T U₀` is at every `i`: the center of `R(t_i)` is that of `H(t_i)`,
which is what lets [1, Prop. 1] put the whole of `R(t_i)`'s center in the error set `E(t)`.

## Inputs
* `A` – dynamics matrix
* `Δt` – time step
* `cs` – constants of the algorithm
* `X₀` – initial set
* `i` – step index

## Hypotheses
* `hU` – the input zonotope is centered at the origin

## Conclusion
* the particular solution is centered at the origin

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
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

theorem STL.depReachAt_Pc_c (A : Mat ℝ n n) (Δt : ℝ) (cs : STL.DepReachConsts n)
    (X₀ : Zonotope (Vec ℝ n)) (hU : cs.U₀.c = 0) (i : ℕ) : -- --- CONCL ---
    (STL.depReachAt A Δt cs X₀ i).Pc.c = 0 := by -- --- PROOF ---
  induction i with
  | zero => rfl
  | succ i ih =>
    show exp (Δt • A) *ᵥ (STL.depReachAt A Δt cs X₀ i).Pc.c + cs.T *ᵥ cs.U₀.c = 0
    rw [ih, hU]; simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
