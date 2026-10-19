module

public import CORALean.ContSet.Zoo.Float.Operations.Basic
public import CORALean.ContSet.Zoo.Float.Theorems.EnclosesIff
public import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter
public import CORALean.ContSet.Interval.Float.Theorems.UminusExact

@[expose] public section

/-!
# `Zoo.uminus` encloses

The Taylor model by `Taylm.uminus_outer`, the interval by `Interval.uminus_exact` (negation is
exact in floats).

## Inputs
* `Z` – zoo
* `f` – function

## Hypotheses
* `h` – `Z` encloses `f`

## Conclusion
* the negated zoo encloses `-f`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.uminus_outer {Z : Zoo 𝕋 n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uminus.Encloses fun t => -f t := by -- --- PROOF ---
  rw [Zoo.encloses_iff] at h ⊢
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hT
    exact Taylm.uminus_outer (h.1 a ha)
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hI
    exact (Interval.uminus_exact a) ▸ Set.neg_mem_neg.2 (h.2 a ha t ht)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
