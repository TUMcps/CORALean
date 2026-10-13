import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestSupport
import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyEqDotProduct
import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff

/-!
# The support function of an ellipsoid

[1, Sec. II (support function)]: `ρ(l | E(q, Q)) = ⟨l, q⟩ + ⟨l, Q l⟩^{1/2}`, the paper's definition
of the ellipsoid. In the generator form `q + G B`, `Q = G Gᵀ` and `⟨l, Q l⟩^{1/2} = ‖Gᵀ l‖₂`, the
value `Ellipsoid.supportBound` stores and attains.

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.supportFunc_eq (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    supportFunc E.construct c = ((dualVec c ⬝ᵥ E.q +
      √(dualVec c ⬝ᵥ (E.shape *ᵥ dualVec c)) : ℝ) : EReal) := by -- --- PROOF ---
  -- `‖Gᵀ l‖₂ = √(lᵀ G Gᵀ l)`
  have hnorm : ‖E.pullback c‖₂ = √(dualVec c ⬝ᵥ (E.shape *ᵥ dualVec c)) := by
    rw [norm₂, Ellipsoid.shape, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
    congr 1
    simp only [dotProduct, sq]
    rfl
  have hval :
      (E.supportBound c).val = dualVec c ⬝ᵥ E.q + √(dualVec c ⬝ᵥ (E.shape *ᵥ dualVec c)) := by
    show c E.q + ‖E.pullback c‖₂ = _
    rw [apply_eq_dotProduct, hnorm]
  rw [← hval]
  obtain ⟨⟨x, hx, hcx⟩, hub⟩ := E.isGreatest_support c
  refine le_antisymm (supportFunc_le_coe_iff.mpr fun y hy => hub ⟨y, hy, rfl⟩) ?_
  rw [← hcx]
  exact le_iSup₂_of_le x hx le_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
