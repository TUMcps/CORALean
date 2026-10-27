module

public import CORALean.ContSet.Interval.Float.Theorems.VecExact
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaEmptySetSound

@[expose] public section

/-!
# `Interval.vec` decides emptiness of an interval matrix

CORA's `representsa(intMat, 'emptySet')` stacks the bounds and tests the stacked interval. A
`true` from the float test on the stacked bounds says the stacked set is empty, and stacking is a
bijection of the entries, so the matrix set is empty.

## Inputs
* `I` – interval matrix

## Hypotheses
* `h` – the float test on the stacked bounds is `true`

## Conclusion
* the interval matrix denotes the empty set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vec_representsa_emptySet_sound {I : Interval (Mat 𝕋 m n)}
    (h : I.vec.representsa_emptySet = true) :
    I.construct = ∅ := by
  have h1 := Interval.representsa_emptySet_sound h
  rw [Interval.vec_exact, Set.image_eq_empty] at h1
  exact h1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
