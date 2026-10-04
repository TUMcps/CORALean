import CORALean.ContSet.Zonotope.Real.Operations.BackReachAligned
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.ShiftMemIff

/-!
# A step of `backReachAligned`, pointwise

`x ∈ Z_{k+1}` exactly when `Ax + K ∈ (Z_k ⊖ Z(Z_k, EW)) ⊕ (-B)U`, for `A` invertible:
`plus`, `mtimes` and `shift` are exact, and the image under `A⁻¹` is the preimage under
`A`. Both directions of [1, Prop. 5] read the step through this.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x ∈ Z_{k+1}` iff `Ax + K` is a point of the difference plus a point of `(-B)U`. -/
theorem Zonotope.mem_backReachAligned_succ_iff {A : Mat ℝ n n} (hA : IsUnit A.det)
    (B : Mat ℝ n m) (K : Vec ℝ n) (U : Zonotope (Vec ℝ m)) (Z₀ : Zonotope (Vec ℝ n))
    (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ)) (k : ℕ) (x : Vec ℝ n) :
    x ∈ (Zonotope.backReachAligned A B K U Z₀ σ (k + 1)).construct ↔
      A *ᵥ x + K ∈ ((Zonotope.backReachAligned A B K U Z₀ σ k).minkDiffAligned
        ((Zonotope.backReachAligned A B K U Z₀ σ k).aligned
          (σ (Zonotope.backReachAligned A B K U Z₀ σ k)).1
          (σ (Zonotope.backReachAligned A B K U Z₀ σ k)).2) rfl).construct
        + ((-B) *ᵥ ·) '' U.construct := by -- --- PROOF ---
  simp only [Zonotope.backReachAligned]
  rw [← Zonotope.mtimes_exact, Set.mem_image, Zonotope.mtimes_exact, Zonotope.plus_exact]
  constructor
  -- `x = A⁻¹y` with `y + K` in the sum, so `Ax = y`
  · rintro ⟨y, hy, rfl⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
    exact (Zonotope.mem_shift_iff _ K y).mp hy
  -- conversely `y = Ax` lies in the shifted sum and `A⁻¹Ax = x`
  · intro hx
    refine ⟨A *ᵥ x, (Zonotope.mem_shift_iff _ K _).mpr hx, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
