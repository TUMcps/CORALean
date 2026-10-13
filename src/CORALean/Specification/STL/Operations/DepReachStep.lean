import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.Specification.STL.Definitions.DepReachConsts
import CORALean.Specification.STL.Definitions.DepReachState
import CORALean.Specification.STL.Operations.DepBox
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Lines 5-7 of the dependency preserving reachability algorithm

[1, Alg. 1], one pass of the loop from `t_i` to `t_{i+1}`: line 5, `C_{i+1} ← e^{AΔt} C_i`; line 6,
`H(t_{i+1}) ← e^{AΔt} H(t_i) ⊕ T ũ` and `D_{i+1} ← interval(e^{AΔt} D_i ⊕ D)`; line 7,
`P_c(t_{i+1}) ← e^{AΔt} P_c(t_i) ⊕ T U₀`. The new generators of `P_c` are appended after the old.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


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
  let Φ := exp (Δt • A)                                              -- e^{AΔt}
  let C' := Zonotope.mtimes Φ s.C                                    -- C_{i+1} ← e^{AΔt} C_i
  -- H(t_{i+1}) ← e^{AΔt} H(t_i) ⊕ T ũ
  let H' := (Zonotope.mtimes Φ s.H).plus (Zonotope.ofPoint (cs.T *ᵥ cs.ũ))
  -- D_{i+1} ← interval(e^{AΔt} D_i ⊕ D)
  let D' := STL.depBox ((Zonotope.mtimes Φ s.D).plus cs.D)
  -- P_c(t_{i+1}) ← e^{AΔt} P_c(t_i) ⊕ T U₀
  let Pc' := (Zonotope.mtimes Φ s.Pc).plus (Zonotope.mtimes cs.T cs.U₀)
  ⟨H', Pc', D', C'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
