import CORALean.ContSet.Zonotope.Real.Operations.Abs
import CORALean.Global.Cost

/-!
# `Zonotope.absCost`

Asserted, not proved: `Operations/Abs.lean` takes the absolute value of the
`n` centre coordinates and of the `n * h` generator entries.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.abs` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.absCost (n h : ℕ) : Cost := ⟨n * (h + 1)⟩

/-- Monotone in the generator count. -/
theorem Zonotope.absCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.absCost n h ≤ Zonotope.absCost n h' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
