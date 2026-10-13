import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `Ellipsoid.isGoodDir`, a sound float test for `isBadDir`

CORA's `@ellipsoid/isBadDir` compares `sqrt(lᵀ Q₁ l)/sqrt(lᵀ Q₂ l)` with `1/max(diag(D))`, the
inverse of the largest generalised eigenvalue from `simdiag`, which rounding cannot decide. A
sound test certifies a bound `μ` on that eigenvalue instead, proposed by the caller: `Q₂ ⪯ μ Q₁`,
as diagonal dominance (Gershgorin) of `M = μ Q₁ - Q₂` with every entry between two directed
roundings, and `μ² lᵀ Q₁ l ≤ lᵀ Q₂ l`, with `lᵀ Q₁ l` rounded up and `lᵀ Q₂ l` down through
`Gᵀ l`. Only `true` is certain, and it says the direction is not bad for the nominal ellipsoids;
`false` says nothing. Gershgorin is conservative: a `Q₁` far from diagonal needs a larger `μ`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The direction `l` is certified not bad, for the eigenvalue bound `μ`. -/
def Ellipsoid.isGoodDir (E₁ E₂ : Ellipsoid 𝕋 n) (l : Vec 𝕋 n) (μ : 𝕋) : Bool :=
  -- the entries of `Q₁ = G₁ G₁ᵀ` and `Q₂ = G₂ G₂ᵀ`, each between two roundings
  let qUp : Ellipsoid 𝕋 n → Fin n → Fin n → 𝕋 := fun E i j =>
    dotUp (fun k => E.G i k) fun k => E.G j k
  let qDown : Ellipsoid 𝕋 n → Fin n → Fin n → 𝕋 := fun E i j =>
    dotDown (fun k => E.G i k) fun k => E.G j k
  -- `M = μ Q₁ - Q₂`, entrywise between its roundings
  let mLo : Fin n → Fin n → 𝕋 := fun i j => subDown (mulDown μ (qDown E₁ i j)) (qUp E₂ i j)
  let mHi : Fin n → Fin n → 𝕋 := fun i j => subUp (mulUp μ (qUp E₁ i j)) (qDown E₂ i j)
  -- every diagonal entry covers the off-diagonal magnitudes of its row
  let dominant : Bool := (List.finRange n).all fun i =>
    le (sumUp fun j => if i = j then zero else maximum (mHi i j) (neg (mLo i j))) (mLo i i)
  -- the entries of `Gᵀ l`, each between two roundings
  let cUp : (E : Ellipsoid 𝕋 n) → Fin E.k → 𝕋 := fun E k => dotUp (fun i => l i) fun i => E.G i k
  let cDown : (E : Ellipsoid 𝕋 n) → Fin E.k → 𝕋 := fun E k =>
    dotDown (fun i => l i) fun i => E.G i k
  -- `lᵀ Q₁ l = ‖G₁ᵀ l‖²` from above and `lᵀ Q₂ l` from below
  let aUp : 𝕋 := sumUp fun k : Fin E₁.k =>
    mulUp (maximum (cUp E₁ k) (neg (cDown E₁ k))) (maximum (cUp E₁ k) (neg (cDown E₁ k)))
  let bDown : 𝕋 := sumDown fun k : Fin E₂.k =>
    mulDown (maximum zero (maximum (cDown E₂ k) (neg (cUp E₂ k))))
      (maximum zero (maximum (cDown E₂ k) (neg (cUp E₂ k))))
  le zero μ && dominant && le (mulUp (mulUp μ μ) aUp) bDown

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
