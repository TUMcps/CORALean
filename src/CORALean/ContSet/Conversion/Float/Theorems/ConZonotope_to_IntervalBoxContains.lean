module

public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_IntervalBox
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotope_to_IntervalCertContains

@[expose] public section

/-!
# The box of every method holds the constrained zonotope

`intervalTight` for every `k`, `intervalCert` at every multiplier, and their intersection, which
is exact (`Interval.intersection_exact`), each hold the set.

## Inputs
* `m` – method of the box
* `cZ` – float constrained zonotope

## Hypotheses
* none

## Conclusion
* the set lies in the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.box_contains (m : ConZonotope.BoxMethod)
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    cZ.toSet ⊆ (cZ.box m).toSet := by -- --- PROOF ---
  cases m with
  | fm k => exact ConZonotope.intervalTight_contains k cZ
  | cert => exact ConZonotope.intervalCertWith_contains cZ _ _
  | both k =>
    intro x hx
    show x ∈ ((cZ.intervalCert).intersection (cZ.intervalTight k)).toSet
    rw [Interval.intersection_exact]
    exact ⟨ConZonotope.intervalCertWith_contains cZ _ _ hx,
      ConZonotope.intervalTight_contains k cZ hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
