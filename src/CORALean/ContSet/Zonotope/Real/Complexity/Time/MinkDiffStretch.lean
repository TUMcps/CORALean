module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.minkDiffStretchCost`

Asserted, not proved: `Operations/MinkDiffStretch.lean` subtracts the centres
(`n`) and scales each of the `h` generators of the minuend by its `μ i`
(`n * h`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.minkDiffStretch` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.minkDiffStretchCost (n h : ℕ) : Cost := ⟨n * (h + 1)⟩

/-- Monotone in the generator count. -/
theorem Zonotope.minkDiffStretchCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.minkDiffStretchCost n h ≤ Zonotope.minkDiffStretchCost n h' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
