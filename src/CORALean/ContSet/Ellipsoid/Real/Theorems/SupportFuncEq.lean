module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestSupport
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# The support function of an ellipsoid

[1, Sec. II (support function)]: `ρ(l | E(q, Q)) = ⟨l, q⟩ + ⟨l, Q l⟩^{1/2}`, the paper's definition
of the ellipsoid: the value `Ellipsoid.supportBound` stores, as CORA's `supportFunc_` does, and
attains (`isGreatest_support`).

## Inputs
* `E` – ellipsoid
* `c` – linear functional

## Hypotheses
* none

## Conclusion
* the support function is `dᵀ q + √(dᵀ Q d)` for the direction `d` of `c`

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.supportFunc_eq (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) : -- --- CONCL ---
    supportFunc E.construct c = ((dualVec c ⬝ᵥ E.q +
      √(dualVec c ⬝ᵥ (E.Q *ᵥ dualVec c)) : ℝ) : EReal) := by -- --- PROOF ---
  have hval :
      (E.supportBound c).val = dualVec c ⬝ᵥ E.q + √(dualVec c ⬝ᵥ (E.Q *ᵥ dualVec c)) := by
    show c E.q + _ = _
    rw [apply_eq_dotProduct]
  rw [← hval]
  obtain ⟨⟨x, hx, hcx⟩, hub⟩ := E.isGreatest_support c
  refine le_antisymm (supportFunc_le_coe_iff.mpr fun y hy => hub ⟨y, hy, rfl⟩) ?_
  rw [← hcx]
  exact le_iSup₂_of_le x hx le_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
