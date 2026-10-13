import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
import CORALean.Global.Cost

/-!
# `Ellipsoid.plusCost`

Asserted, not proved: `Operations/Plus.lean` scales every entry of both
generator matrices before laying them side by side — `n * q₁` multiplications
for `s₁ • G₁`, `n * q₂` for `s₂ • G₂` — and `Fin.append` is free.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Ellipsoid.plus` costs at `Vec ℝ n` on `q₁`, `q₂` generators: one
multiplication per generator entry, either scaling. -/
def Ellipsoid.plusCost (n q₁ q₂ : ℕ) : Cost := ⟨n * (q₁ + q₂)⟩

/-- Monotone in both generator counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem Ellipsoid.plusCost_mono {q₁ q₁' q₂ q₂' : ℕ} (n : ℕ) (h1 : q₁ ≤ q₁') (h2 : q₂ ≤ q₂') :
    Ellipsoid.plusCost n q₁ q₂ ≤ Ellipsoid.plusCost n q₁' q₂' :=
  Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
