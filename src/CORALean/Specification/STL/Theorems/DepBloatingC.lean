module

public import CORALean.Specification.STL.Operations.DepBloating

@[expose] public section

/-!
# The bloating is centered at the origin

[1, Prop. 1]: every term of `D` is a map of `U₀` (by a matrix or an interval matrix), centered
at the image of the center of `U₀`, so `D` is centered at `0` when `U₀` is, as `B(U ⊕ (-c_u))` is.

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

open CORALean.Real Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The center of the Minkowski sum of the images, folded from a center-`0` start. -/
theorem STL.aux_foldl_c (A : Mat ℝ n n) (U₀ : Zonotope (Vec ℝ n)) (Δt : ℝ) (hU : U₀.c = 0)
    (l : List ℕ) (Z : Zonotope (Vec ℝ n)) (hZ : Z.c = 0) :
    (l.foldl (fun Z j => Z.plus (Zonotope.mtimes (MatExp.particularCoeff A Δt (j + 1)) U₀))
      Z).c = 0 := by -- --- PROOF ---
  induction l generalizing Z with
  | nil => exact hZ
  | cons j l ih =>
    refine ih _ ?_
    show Z.c + MatExp.particularCoeff A Δt (j + 1) *ᵥ U₀.c = 0
    rw [hZ, hU]; simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depBloating_c (A : Mat ℝ n n) (U₀ : Zonotope (Vec ℝ n)) (Δt : ℝ) (κ : ℕ)
    (hU : U₀.c = 0) : (STL.depBloating A U₀ Δt κ).c = 0 := by
  have h2 := STL.aux_foldl_c A U₀ Δt hU (List.range κ) (Zonotope.ofPoint 0) rfl
  show _ + _ + _ = 0
  simp only [Zonotope.mtimes, Zonotope.mtimesIntervalMat, hU, Matrix.mulVec_zero] at h2 ⊢
  rw [h2]; simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
