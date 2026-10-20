module

public import CORALean.ContSet.SpectraShadow.Float.Operations.Empty
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero

@[expose] public section

/-!
# `SpectraShadow.empty` denotes the empty set

The stored constant reads as `-1`, and `-1 ⪰ 0` is met by no coefficient family, its diagonal
being negative; the nominal part is `∅`, and so is its sum with the error box.

## Inputs
* `n` – natural number

## Hypotheses
* none

## Conclusion
* `SpectraShadow.empty` denotes the empty set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.empty_exact (n : ℕ) :
    (SpectraShadow.empty n : SpectraShadow 𝕋 (Vec 𝕋 n)).construct = ∅ := by -- --- PROOF ---
  -- the nominal part is empty: its inequality has a negative diagonal
  have hN : InflatedContSet.nominalSet (SpectraShadow.empty n : SpectraShadow 𝕋 (Vec 𝕋 n)) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨β, hβ, -⟩ := SpectraShadow.mem_nominalSet_iff.mp hx
    have hA : ∀ i, toRealMat ((SpectraShadow.empty (𝕋 := 𝕋) n).A i) = 0 := fun i =>
      SpectraShadow.toRealMat_const_zero
    simp only [hA, smul_zero, Finset.sum_const_zero, add_zero] at hβ
    have h := Matrix.PosSemidef.diag_nonneg (i := (0 : Fin 1)) hβ
    simp [toRealMat, SpectraShadow.empty, toReal_neg, toReal_one] at h
    norm_num at h
  show InflatedContSet.nominalSet (SpectraShadow.empty n : SpectraShadow 𝕋 (Vec 𝕋 n))
      + (SpectraShadow.empty n : SpectraShadow 𝕋 (Vec 𝕋 n)).I_error.construct = _
  rw [hN, Set.empty_add]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
