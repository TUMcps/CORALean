module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.isGoodDir`, a sound float test for `isBadDir`

CORA's `@ellipsoid/isBadDir` compares `sqrt(lᵀ Q₁ l)/sqrt(lᵀ Q₂ l)` with `1/max(diag(D))`, the
inverse of the largest generalised eigenvalue from `simdiag`, which rounding cannot decide. A
sound test certifies a bound `μ` on that eigenvalue instead, proposed by the caller: `Q₂ ⪯ μ Q₁`,
as diagonal dominance (Gershgorin) of `M = μ Q₁ - Q₂` with every entry between two directed
roundings, and `μ² lᵀ Q₁ l ≤ lᵀ Q₂ l`, with `lᵀ Q₁ l` rounded up (`quadUp`) and `lᵀ Q₂ l` down
(`quadDown`). Only `true` is certain, and it says the direction is not bad for the nominal
ellipsoids; `false` says nothing. Gershgorin is conservative: a `Q₁` far from diagonal needs a
larger `μ`.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The direction `l` is certified not bad, for the eigenvalue bound `μ`. -/
def Ellipsoid.isGoodDir (E₁ E₂ : Ellipsoid 𝕋 n) (l : Vec 𝕋 n) (μ : 𝕋) : Bool :=
  -- `M = μ Q₁ - Q₂`, entrywise between its roundings
  let mLo : Fin n → Fin n → 𝕋 := fun i j => subDown (mulDown μ (E₁.Q i j)) (E₂.Q i j)
  let mHi : Fin n → Fin n → 𝕋 := fun i j => subUp (mulUp μ (E₁.Q i j)) (E₂.Q i j)
  -- every diagonal entry covers the off-diagonal magnitudes of its row
  let dominant : Bool := (List.finRange n).all fun i =>
    le (sumUp fun j => if i = j then zero else maximum (mHi i j) (neg (mLo i j))) (mLo i i)
  le zero μ && dominant && le (mulUp (mulUp μ μ) (E₁.quadUp l)) (E₂.quadDown l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
