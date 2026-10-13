module

public import CORALean.ContSet.ConPolyZono.Float.Operations.SplitDepFactor
public import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetOuter
public import CORALean.ContSet.ConPolyZono.Real.Theorems.SplitDepFactorUnion

@[expose] public section

/-!
# `ConPolyZono.splitDepFactor` covers the set

The exact layer's halves of the stored set cover it exactly (`splitDepFactor_union`),
`getSubset_outer` carries each half, with the error box, into the float half, and `∓1/2` and `1/2`
read back as themselves. Outer, not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.splitDepFactor_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.p) :
    cPZ.construct ⊆
      (cPZ.splitDepFactor k).1.construct ∪ (cPZ.splitDepFactor k).2.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  -- the half and the negated half, read back as reals
  have hc : toReal (neg (half (one : 𝕋))) = -(2 : ℝ)⁻¹ := by
    rw [toReal_neg, toReal_half, toReal_one]; norm_num
  have hr : toReal (half (one : 𝕋)) = (2 : ℝ)⁻¹ := by
    rw [toReal_half, toReal_one]; norm_num
  -- the point is in one of the exact halves of the stored set
  have hz' : z ∈ (nominal cPZ).construct := hz
  rw [← Real.ConPolyZono.splitDepFactor_union (nominal cPZ) k] at hz'
  rcases hz' with h | h
  · refine Or.inl (ConPolyZono.getSubset_outer cPZ k _ _ ⟨z, ?_, e, he, rfl⟩)
    rw [hc, hr]
    exact h
  · refine Or.inr (ConPolyZono.getSubset_outer cPZ k _ _ ⟨z, ?_, e, he, rfl⟩)
    rw [hr]
    exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
