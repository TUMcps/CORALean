module

public import CORALean.HybridDynamics.Operations.TimeIntervalStep

@[expose] public section

/-!
# `Location.timeIntervalStepInv`

The stay enclosure cut by the invariant. `Intersection.intersection` intersects with `ℓ.inv`
after `Plus.plus` has already added the input contribution `Ud` in, not
before: the invariant holds of the two added together, and cutting the
homogeneous part alone before the addition would not be sound.

Takes `Ud` for that reason — the cut cannot be stated over `X₀` alone.

`Intersection.intersection` is homogeneous, so this is where a location's invariant has to be in
the state's own family: `Location S S L 𝕋 n`, not the general `S G` (#39).
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stay enclosure over `X₀` and `Ud`, cut down to the location's invariant. -/
noncomputable def Location.timeIntervalStepInv [∀ n, Intersection (S n) (Vec ℝ n)]
    (ℓ : Location S S L 𝕋 n) (r : ℝ) (η : ℕ) (X₀ Ud : S n) : S n :=
  Intersection.intersection (Plus.plus (ℓ.timeIntervalStep r η X₀) Ud) ℓ.inv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
