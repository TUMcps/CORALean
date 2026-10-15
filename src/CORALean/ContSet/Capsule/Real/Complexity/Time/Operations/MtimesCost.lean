module

public import CORALean.ContSet.Capsule.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` computes the Frobenius norm of
`M` (`m * n` products, `m * n` additions, one `sqrt`), sends the centre and the
generator through `M *ᵥ ·` (two `Cost.matVec m n`) and scales the radius (one
product): `6 * m * n + 2`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.mtimes` costs at `M : Mat ℝ m n`. -/
def Capsule.mtimesCost (m n : ℕ) : Cost := ⟨2 * (m * n) + 1⟩ + (2 : ℕ) • Cost.matVec m n + ⟨1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
