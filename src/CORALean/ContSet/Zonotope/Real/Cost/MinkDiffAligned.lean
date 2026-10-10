import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
import CORALean.Global.Cost

/-!
# `Zonotope.minkDiffAlignedCost`

Asserted, not proved: `Operations/MinkDiffAligned.lean` subtracts the centres
and the `h` generators pairwise, `n * (h + 1)` subtractions at `Vec ℝ n`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffAligned` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.minkDiffAlignedCost (n h : ℕ) : Cost := ⟨n * (h + 1)⟩

/-- Monotone in the generator count. -/
theorem Zonotope.minkDiffAlignedCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.minkDiffAlignedCost n h ≤ Zonotope.minkDiffAlignedCost n h' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
