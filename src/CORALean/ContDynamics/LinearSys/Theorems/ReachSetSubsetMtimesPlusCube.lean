import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq
import CORALean.ContDynamics.LinearSys.Theorems.NormLeOfMemInputReach
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.Cube
import CORALean.ContSet.Zonotope.Real.Theorems.CubeExact
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# One step of the flow, enclosed by a zonotope

[1, Lemma 1], first half: `Φ_r(Z) ⊆ e^{rA}Z + □(β_r)`, `β_r = (e^{r‖A‖} - 1)/‖A‖ · µ`, for
`x' = Ax + u`, `‖u‖ ≤ µ`. `Φ_r(Z)` is the set every solution from `Z` is at after `r`,
`reachSet` on `[0, r]`: a solution in Carathéodory's sense, the input merely
measurable, which is the widest reading of [1]'s "solution of (1)"; the set is then
exactly `e^{rA}Z ⊕ inputReach U r` (`reachSet_eq`), and every point of
`inputReach U r` lies in `□(β_r)` (`norm_le_of_mem_inputReach`, eq. 3 of [1]).

`‖u‖ ≤ µ` is `U` being the ball of radius `µ`, as a zonotope; `0 < ‖A‖` is [1]'s division by
`‖A‖`, without which `β_r` reads `0 / 0` in Lean.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1], conservative approximation: `Φ_r(Z) ⊆ e^{rA}Z + □(β_r)`. -/
theorem LinearSys.reachSet_subset_mtimes_plus_cube (sys : LinearSys 𝕋 n)
    (Z U : Zonotope (Vec ℝ n)) {μ r : ℝ} (hA : 0 < ‖toRealMat sys.A‖) (hr : 0 ≤ r)
    (hμ : 0 ≤ μ) (hU : U.construct = Metric.closedBall 0 μ) :
    sys.reachSet (S := 𝒵) (Set.Icc 0 r) Z U r
      ⊆ ((Z.mtimes (exp (r • toRealMat sys.A))).plus
          (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖
            * μ))).construct := by -- --- PROOF ---
  have hx := Real.add_one_le_exp (r * ‖toRealMat sys.A‖)
  have hx0 := mul_nonneg hr hA.le
  have hβ : 0 ≤ (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖ * μ :=
    mul_nonneg (div_nonneg (by linarith) hA.le) hμ
  rw [sys.reachSet_eq (S := 𝒵) Z U hr (Zonotope.isBounded_construct U)]
  rintro _ ⟨_, ⟨z, hz, rfl⟩, v, hv, rfl⟩
  rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact, Zonotope.cube_exact n hβ]
  refine ⟨_, ⟨z, hz, rfl⟩, v, mem_closedBall_zero_iff.mpr ?_, rfl⟩
  exact sys.norm_le_of_mem_inputReach hA hr (fun u hu => by
    have : u ∈ Metric.closedBall (0 : Vec ℝ n) μ := hU ▸ hu
    exact mem_closedBall_zero_iff.mp this) hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
