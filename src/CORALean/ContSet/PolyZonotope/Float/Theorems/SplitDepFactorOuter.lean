import CORALean.ContSet.PolyZonotope.Float.Operations.SplitDepFactor
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitDepFactorUnion

/-!
# `PolyZonotope.splitDepFactor` covers the set

The exact layer's halves of the stored set cover it exactly (`splitDepFactor_union`),
`getSubset_outer` carries each half, with the error box, into the float half, and `∓1/2` and `1/2`
read back as themselves. Outer, not exact.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitDepFactor_outer (pZ : PolyZonotope 𝕋 n) (k : Fin pZ.p) :
    pZ.construct ⊆
      (pZ.splitDepFactor k).1.construct ∪ (pZ.splitDepFactor k).2.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  -- the half and the negated half, read back as reals
  have hc : toReal (neg (half (one : 𝕋))) = -(2 : ℝ)⁻¹ := by
    rw [toReal_neg, toReal_half, toReal_one]; norm_num
  have hr : toReal (half (one : 𝕋)) = (2 : ℝ)⁻¹ := by
    rw [toReal_half, toReal_one]; norm_num
  -- the point is in one of the exact halves of the stored set
  have hz' : z ∈ (nominal pZ).construct := hz
  rw [← Real.PolyZonotope.splitDepFactor_union (nominal pZ) k] at hz'
  rcases hz' with h | h
  · refine Or.inl (PolyZonotope.getSubset_outer pZ k _ _ ⟨z, ?_, e, he, rfl⟩)
    rw [hc, hr]
    exact h
  · refine Or.inr (PolyZonotope.getSubset_outer pZ k _ _ ⟨z, ?_, e, he, rfl⟩)
    rw [hr]
    exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
