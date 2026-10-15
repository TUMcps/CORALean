module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Ellipsoid.plusCost`

Asserted, not proved: `Operations/Plus.lean` scales every entry of both
generator matrices before laying them side by side — `n * q₁` multiplications
for `s₁ • G₁`, `n * q₂` for `s₂ • G₂` — and `Fin.append` computes nothing. The center sum is `n`
additions, and the `n * (1 + q₁ + q₂)`
entries of the result are written.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Ellipsoid.plus` costs at `Vec ℝ n` on `q₁`, `q₂` generators: `n` additions for the
center, one multiplication per generator entry, either scaling, and a write for each of the
`n * (1 + q₁ + q₂)` entries of the result. -/
def Ellipsoid.plusCost (n q₁ q₂ : ℕ) : Cost := ⟨n + n * (q₁ + q₂) + n * (1 + q₁ + q₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
