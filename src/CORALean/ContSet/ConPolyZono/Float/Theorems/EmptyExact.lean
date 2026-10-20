module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Empty
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# `ConPolyZono.empty` denotes the empty set

The nominal part is `∅`: its single constraint row asks `|(A μ)₀ - 1| ≤ |0|` of an empty matrix,
`one` and `zero` reading as `1` and `0`. So the sum with the error box is `∅` too.

## Inputs
* `n` – ambient dimension

## Hypotheses
* none

## Conclusion
* the set is empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.empty_exact (n : ℕ) :
    (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n)).construct = ∅ := by -- --- PROOF ---
  have hN : InflatedContSet.nominalSet (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n)) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rw [ConPolyZono.mem_nominalSet_iff]
    rintro ⟨a, β, -, -, hsat, -⟩
    -- the one row reads `|0 - 1| ≤ |0|`
    have h := ((PolyLevelSet.mem_construct_iff_of_eq
      (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n)).cons_eq).mp hsat).2 (0 : Fin 1)
    simp [ConPolyZono.empty, Matrix.mulVec, toReal_one, toReal_zero] at h
    exact absurd h (by norm_num)
  show InflatedContSet.nominalSet (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n))
      + (ConPolyZono.empty n : ConPolyZono 𝕋 (Vec 𝕋 n)).I_error.construct = _
  rw [hN, Set.empty_add]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
