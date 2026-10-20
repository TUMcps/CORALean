module

public import CORALean.ContSet.ConZonotope.Float.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.centerLo` and `centerHi` bracket `c + G β₀`

The two ends are a rounded-down and a rounded-up evaluation of the same expression.

## Inputs
* `cZ` – float constrained zonotope
* `β₀` – coefficient point
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* the evaluated center lies between its two roundings
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.center_between (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (β₀ : Vec 𝕋 cZ.h)
    (i : Fin n) : -- --- CONCL ---
    toReal (cZ.centerLo β₀ i) ≤ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j)
      ∧ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (β₀ j)
        ≤ toReal (cZ.centerHi β₀ i) := by -- --- PROOF ---
  have h1 := addDown_le_add (cZ.c i) (dotDown (fun j => cZ.G j i) β₀)
  have h2 := add_le_addUp (cZ.c i) (dotUp (fun j => cZ.G j i) β₀)
  have h3 := dotDown_le (fun j => cZ.G j i) β₀
  have h4 := le_dotUp (fun j => cZ.G j i) β₀
  exact ⟨by simp only [ConZonotope.centerLo]; linarith,
    by simp only [ConZonotope.centerHi]; linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
