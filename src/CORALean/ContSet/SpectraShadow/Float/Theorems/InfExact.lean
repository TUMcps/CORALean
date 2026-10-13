import CORALean.ContSet.Interval.Float.Theorems.OriginExact
import CORALean.ContSet.SpectraShadow.Float.Operations.Inf
import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero

/-!
# `SpectraShadow.Inf` denotes everything

The stored constant reads as `1`, the generators as the unit vectors, and the error box is the
origin box. The inequality `1 ⪰ 0` is met by every coefficient family, whose variables are then
read off the point.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The nominal inequality of `Inf`, whatever the coefficients. -/
theorem SpectraShadow.aux_inf_lmi (n : ℕ) (β : Fin (SpectraShadow.Inf (𝕋 := 𝕋) n).m → ℝ) :
    (toRealMat (SpectraShadow.Inf (𝕋 := 𝕋) n).A₀
      + ∑ i, β i • toRealMat ((SpectraShadow.Inf (𝕋 := 𝕋) n).A i)) = 1 := by -- --- PROOF ---
  -- every `Aᵢ` is the zero matrix, so the combination is `A₀`
  have hA : ∀ i, toRealMat ((SpectraShadow.Inf (𝕋 := 𝕋) n).A i) = 0 := fun i =>
    SpectraShadow.toRealMat_const_zero
  simp only [hA, smul_zero, Finset.sum_const_zero, add_zero]
  -- and `A₀` is the `1 × 1` identity
  ext a b
  fin_cases a; fin_cases b
  simp [toRealMat, SpectraShadow.Inf, toReal_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.Inf_exact (n : ℕ) :
    (SpectraShadow.Inf n : SpectraShadow 𝕋 (Vec 𝕋 n)).construct = Set.univ := by -- --- PROOF ---
  -- the nominal part is everything: the coefficients are the point itself
  have hN : InflatedContSet.nominalSet (SpectraShadow.Inf n : SpectraShadow 𝕋 (Vec 𝕋 n)) =
    Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    refine SpectraShadow.mem_nominalSet_iff.mpr
      ⟨fun i => x ⟨i.1, i.2⟩, ?_, fun i => ?_⟩
    · rw [SpectraShadow.aux_inf_lmi]
      exact Matrix.PosSemidef.one
    · -- the generators read as the unit vectors
      have h : ∀ j : Fin n, toReal (if i.val = j.val then (one : 𝕋) else zero)
          = if i = j then 1 else 0 := by
        intro j
        by_cases hij : i = j
        · simp [hij, toReal_one]
        · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
          simp [hij, this, toReal_zero]
      simp [SpectraShadow.Inf, toReal_zero, h]
  -- the box is the origin, so the sum is unchanged
  show InflatedContSet.nominalSet (SpectraShadow.Inf n : SpectraShadow 𝕋 (Vec 𝕋 n))
      + (SpectraShadow.Inf n : SpectraShadow 𝕋 (Vec 𝕋 n)).E.construct = _
  rw [hN]
  have hE : (SpectraShadow.Inf n : SpectraShadow 𝕋 (Vec 𝕋 n)).E.construct = {0} :=
    Interval.origin_exact n
  rw [hE]
  simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
