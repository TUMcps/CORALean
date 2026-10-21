module

public import CORALean.HybridDynamics.Operations.TimeInterval

@[expose] public section

/-!
# `Location.timeIntervalInv`

The stay enclosure cut by the invariant. `Intersection.intersection` intersects with `ℓ.inv`
after `Plus.plus` has added the input contribution `Ud`, not before: the invariant holds of the two
added together, and cutting the homogeneous part alone before the addition would not be sound, so
the cut cannot be stated over `X₀` alone. `Intersection.intersection` is homogeneous, so a
location's invariant has to be in the state's own family: `Location S S L 𝕋 n`, not `S G` (#39).

## Inputs
* `ℓ` – location
* `r` – time step
* `η` – Taylor order
* `X₀` – initial set
* `Ud` – input contribution

## Output
* stay enclosure cut by the invariant
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
noncomputable def Location.timeIntervalInv [∀ n, Intersection (S n) (Vec ℝ n)]
    (ℓ : Location S S L 𝕋 n) (r : ℝ) (η : ℕ) (X₀ Ud : S n) : S n :=
  Intersection.intersection (Plus.plus (ℓ.timeInterval r η X₀) Ud) ℓ.inv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
