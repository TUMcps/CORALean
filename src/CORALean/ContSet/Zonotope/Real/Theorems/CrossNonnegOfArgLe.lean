module

public import CORALean.ContSet.Zonotope.Real.Theorems.CrossEqNormMulSin

@[expose] public section

/-!
# Angle order gives the sign of a cross product

For two vectors in the upper half-plane, `cross(u, w) = ‖u‖ ‖w‖ sin(θ_w - θ_u)` and the angles
`θ = arg` lie in `[0, π]`, so `θ_u ≤ θ_w` makes the cross product nonnegative. It is what turns
the trigonometric sort of [1, Alg. 3] and the pivot split of [1, Alg. 4] into the sign
conditions the walk of a zonogon is proved from.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cross_nonneg_of_arg_le {u w : Vec ℝ 2} (hu : 0 ≤ u 1)
    (h : Complex.arg ⟨u 0, u 1⟩ ≤ Complex.arg ⟨w 0, w 1⟩) :
    0 ≤ u 0 * w 1 - u 1 * w 0 := by
  rw [Zonotope.cross_eq_norm_mul_sin]
  have h0 : 0 ≤ Complex.arg ⟨u 0, u 1⟩ := Complex.arg_nonneg_iff.mpr hu
  have h1 := Complex.arg_le_pi (⟨w 0, w 1⟩ : ℂ)
  exact mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
