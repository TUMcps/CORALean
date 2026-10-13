import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import CORALean.Global.Tensor

/-!
# The planar cross product is the product of the norms and the sine

`cross(u, w) = ‖u‖ ‖w‖ sin(θ_w - θ_u)` for the angles `θ = arg`, read through the complex number
`x + i y`. It is what the angle order of [1, Alg. 3] and [1, Alg. 4] is turned into a sign by.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A vector is its norm times the cosine and sine of its argument. -/
theorem Zonotope.aux_polar (u : Vec ℝ 2) :
    u 0 = ‖(⟨u 0, u 1⟩ : ℂ)‖ * Real.cos (Complex.arg ⟨u 0, u 1⟩) ∧
    u 1 = ‖(⟨u 0, u 1⟩ : ℂ)‖ * Real.sin (Complex.arg ⟨u 0, u 1⟩) :=
  ⟨(Complex.norm_mul_cos_arg ⟨u 0, u 1⟩).symm, (Complex.norm_mul_sin_arg ⟨u 0, u 1⟩).symm⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cross_eq_norm_mul_sin (u w : Vec ℝ 2) :
    u 0 * w 1 - u 1 * w 0 = ‖(⟨u 0, u 1⟩ : ℂ)‖ * ‖(⟨w 0, w 1⟩ : ℂ)‖ *
      Real.sin (Complex.arg ⟨w 0, w 1⟩ - Complex.arg ⟨u 0, u 1⟩) := by -- --- PROOF ---
  obtain ⟨hu0, hu1⟩ := Zonotope.aux_polar u
  obtain ⟨hw0, hw1⟩ := Zonotope.aux_polar w
  rw [Real.sin_sub]
  generalize ‖(⟨u 0, u 1⟩ : ℂ)‖ = ru at hu0 hu1 ⊢
  generalize ‖(⟨w 0, w 1⟩ : ℂ)‖ = rw at hw0 hw1 ⊢
  generalize Complex.arg ⟨u 0, u 1⟩ = tu at hu0 hu1 ⊢
  generalize Complex.arg ⟨w 0, w 1⟩ = tw at hw0 hw1 ⊢
  linear_combination (w 1) * hu0 + (ru * Real.cos tu) * hw1 - (w 0) * hu1 -
    (ru * Real.sin tu) * hw0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
