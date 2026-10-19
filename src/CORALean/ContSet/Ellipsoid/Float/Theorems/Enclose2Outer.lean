module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic

@[expose] public section

/-!
# `Ellipsoid.enclose₂` contains the segments

Both ends of a segment are in the hull by its contract, and the float hull is convex.

## Inputs
* `orOA` – outer hull of two ellipsoids
* `E` – ellipsoid
* `E2` – ellipsoid

## Hypotheses
* `hor` – `orOA` contains both operands

## Conclusion
* the linear combination of `E` and `E2` lies in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.enclose₂_outer (orOA : Ellipsoid 𝕋 n → Ellipsoid 𝕋 n → Ellipsoid 𝕋 n)
    (hor : ∀ E₁ E₂, E₁.construct ∪ E₂.construct ⊆ (orOA E₁ E₂).construct)
    (E E2 : Ellipsoid 𝕋 n) :
    Set.linComb E.construct E2.construct ⊆ (Ellipsoid.enclose₂ orOA E E2).construct := by
  rintro _ ⟨y₁, h₁, y₂, h₂, l, ⟨hl0, hl1⟩, rfl⟩
  exact (Ellipsoid.convex_construct _) (hor _ _ (Or.inl h₁)) (hor _ _ (Or.inr h₂)) hl0
    (by linarith) (by ring)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
