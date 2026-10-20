module

public import CORALean.ContSet.Interval.Float.Operations.OfBounds

@[expose] public section

/-!
# `Interval.ofBounds` encloses, over a floating-point scalar

Nothing rounds: each bound was already rounded outward where it was computed,
and negating a float is exact.

## Inputs
* none

## Hypotheses
* `up` – upper bounds of `S`, one per coordinate
* `lo` – negated lower bounds of `S`, one per coordinate

## Conclusion
* `S` lies in the box built from the bounds
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {S : Set (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.subset_ofBounds (up : ∀ j, FloatBound 𝕋 S (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 S (-LinearMap.proj j)) :
    S ⊆ (Interval.ofBounds up lo).construct := by -- --- PROOF ---
  intro x hx j
  constructor
  · have h : -(x j) ≤ toReal (lo j).val := (lo j).le x hx
    show toReal (neg (lo j).val) ≤ x j
    rw [toReal_neg]
    linarith
  · exact (up j).le x hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
