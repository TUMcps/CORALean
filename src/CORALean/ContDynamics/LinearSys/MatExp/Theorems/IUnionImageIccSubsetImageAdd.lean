module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMulVecImageSubsetAddImage2
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IUnionImageIccEqImage

@[expose] public section

/-!
# The reach set over `[kr, (k+1)r]` lies in `e^{Akr}(Z + ΔR)`

`[1, Eq. 6]`: the propagated enclosure of the input-free reach set of `Z`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reach set over `[kr, (k+1)r]` lies in `e^{Akr}(Z + ΔR)`. -/
theorem MatExp.iUnion_image_Icc_subset_image_add (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (k : ℕ) (Z : Set (Vec ℝ n)) :
    (⋃ t ∈ Set.Icc ((k : ℝ) * r) (((k : ℝ) + 1) * r), (fun x => exp (t • A) *ᵥ x) '' Z)
      ⊆ (fun y => exp (((k : ℝ) * r) • A) *ᵥ y) ''
        (Z + Set.image2 (fun B x => B *ᵥ x) (MatExp.expDiffMatrices A r m) Z) := by -- --- PROOF ---
  rw [MatExp.iUnion_image_Icc_eq_image]
  refine Set.image_mono ?_
  refine Set.iUnion₂_subset fun t ht => ?_
  exact MatExp.expMulVec_image_subset_add_image2 A hr hε ht.1 ht.2 Z


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
