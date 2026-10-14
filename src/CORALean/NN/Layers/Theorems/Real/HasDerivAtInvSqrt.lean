module

public import CORALean.NN.Layers.Theorems.Real.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# The clamped inverse square root's derivative above the clamp

Above the clamp the function is `(Real.sqrt ·)⁻¹`, whose derivative `Real.hasDerivAt_sqrt` and
`HasDerivAt.inv` give; the agreement moves it across on a neighbourhood of `x`, all above `1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem hasDerivAt_invSqrt {x : ℝ} (hx : 1 < x) :
    HasDerivAt invSqrt (-(2 * x * Real.sqrt x)⁻¹) x := by -- --- PROOF ---
  have heq : invSqrt =ᶠ[nhds x] (fun y => (Real.sqrt y)⁻¹) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [invSqrt_eq_of_one_le hy.le]
  rw [heq.hasDerivAt_iff]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := hxpos.ne'
  have hd := (Real.hasDerivAt_sqrt hxne).inv (Real.sqrt_ne_zero'.mpr hxpos)
  have hval : -(1 / (2 * Real.sqrt x)) / Real.sqrt x ^ 2 = -(2 * x * Real.sqrt x)⁻¹ := by
    rw [Real.sq_sqrt hxpos.le]
    field_simp
  rwa [hval] at hd

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
