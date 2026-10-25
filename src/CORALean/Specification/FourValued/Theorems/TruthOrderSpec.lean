module

public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# The truth order of the four values

`v ⊑ₜ v'` means that `v` is less true than `v'`: `⊥ ⊑ₜ ⊣₁ ⊑ₜ ⊤` and `⊥ ⊑ₜ ⊣₂ ⊑ₜ ⊤`, with `⊣₁` and
`⊣₂` incomparable ([1, Sec. 2.2 (order)]). The order on `U₁` is the restriction of this one
(`FourValued.fromKleene_le_iff`) and that of the stored codes (`Kleene.le_iff_code`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* false is below unknown and inconclusive, which are below true and incomparable

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValued.truthOrder_spec :
    (FourValued.ff ≤ FourValued.uu ∧ FourValued.uu ≤ FourValued.tt) ∧
    (FourValued.ff ≤ FourValued.ii ∧ FourValued.ii ≤ FourValued.tt) ∧
    ¬ FourValued.uu ≤ FourValued.ii ∧ ¬ FourValued.ii ≤ FourValued.uu := by
  simp [FourValued.le_iff]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
