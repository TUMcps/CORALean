module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.Specification.STL.Definitions.DepReachConsts
public import CORALean.Specification.STL.Definitions.DepReachState
public import CORALean.Specification.STL.Operations.DepBox
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# Lines 5-7 of the dependency preserving reachability algorithm

[1, Alg. 1], one pass of the loop from `t_i` to `t_{i+1}`: line 5, `C_{i+1} ← e^{AΔt} C_i`; line 6,
`H(t_{i+1}) ← e^{AΔt} H(t_i) ⊕ T ũ` and `D_{i+1} ← interval(e^{AΔt} D_i ⊕ D)`; line 7,
`P_c(t_{i+1}) ← e^{AΔt} P_c(t_i) ⊕ T U₀`. The new generators of `P_c` are appended after the old.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (a zonotope
computation over `𝕋` with directed rounding) is not yet written.

## Inputs
* `A` – dynamics matrix
* `Δt` – time step
* `cs` – constants of the algorithm
* `s` – algorithm state

## Output
* the algorithm state one step later

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 5-7 of [1, Alg. 1]. -/
noncomputable def STL.depReachStep (A : Mat ℝ n n) (Δt : ℝ) (cs : STL.DepReachConsts n)
    (s : STL.DepReachState n) : STL.DepReachState n :=
  -- 5. `e^{AΔt}`, which lines 5-7 apply to every set
  let Φ := exp (Δt • A)
  -- 5. `C_{i+1} ← e^{AΔt} C_i`
  let C' := Zonotope.mtimes Φ s.C
  -- 6. `H(t_{i+1}) ← e^{AΔt} H(t_i) ⊕ T ũ`
  let H' := (Zonotope.mtimes Φ s.H).plus (Zonotope.ofPoint (cs.T *ᵥ cs.ũ))
  -- 6. `D_{i+1} ← interval(e^{AΔt} D_i ⊕ D)`
  let D' := STL.depBox ((Zonotope.mtimes Φ s.D).plus cs.D)
  -- 7. `P_c(t_{i+1}) ← e^{AΔt} P_c(t_i) ⊕ T U₀`
  let Pc' := (Zonotope.mtimes Φ s.Pc).plus (Zonotope.mtimes cs.T cs.U₀)
  ⟨H', Pc', D', C'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
