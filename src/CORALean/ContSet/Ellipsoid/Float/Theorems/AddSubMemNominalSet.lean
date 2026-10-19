module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructSubsetOfLe
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic

@[expose] public section

/-!
# A dominated ellipsoid moved to the stored center lies in the nominal part

What an enclosing float operation is sound by: its exact result is a real ellipsoid `F`, and the
stored `Q` either dominates `F`'s shape (`Q - F.Q` positive semi-definite, `Operations/Inflate`),
or `F` is a point. In the first case `Q` is positive semi-definite, the nominal part is the
ellipsoid of `Q`, and it contains `F`'s shape about the stored center
(`construct_subset_of_le`); in the second only the center is asked for, which every nominal part
holds.

## Inputs
* `E` – float ellipsoid
* `F` – real ellipsoid
* `x` – point of `F`

## Hypotheses
* `hF` – `F` is a point or `Q` dominates its shape
* `hx` – `x` in `F`

## Conclusion
* `x` moved to the stored center lies in the nominal part
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `F` about the stored center lies in the nominal part when `Q` dominates it or it is a point. -/
theorem Ellipsoid.add_sub_mem_nominalSet {E : Ellipsoid 𝕋 n} {F : Real.Ellipsoid n}
    (hF : F.Q = 0 ∨ (toRealMat E.Q - F.Q).PosSemidef) {x : Vec ℝ n} (hx : x ∈ F.construct) :
    toRealVec E.q + (x - F.q) ∈ nominalSet E := by -- --- PROOF ---
  obtain ⟨u, hu, rfl⟩ := Real.Ellipsoid.mem_construct_iff.1 hx
  rw [add_sub_cancel_left]
  rcases hF with h0 | hdom
  · -- a point: only the center
    rw [(F.G_eq_zero_iff).2 h0, zero_mulVec, add_zero]
    exact Ellipsoid.mem_nominalSet_iff.mpr ⟨0, by rw [norm₂_zero]; exact zero_le_one,
      by rw [mulVec_zero, add_zero]⟩
  · -- dominated: `Q` is positive semi-definite, and its ellipsoid contains `F`'s shape
    have hpsd : (toRealMat E.Q).PosSemidef := by
      have := F.psd.add hdom
      rwa [add_sub_cancel] at this
    have hsub := Real.Ellipsoid.construct_subset_of_le (E₁ := ⟨F.Q, toRealVec E.q, F.psd⟩)
      (E₂ := ⟨toRealMat E.Q, toRealVec E.q, hpsd⟩) hdom rfl
    show _ ∈ (nominal E).ellipsoid.construct
    rw [Ellipsoid.nominal_of_psd hpsd]
    exact hsub (Real.Ellipsoid.mem_construct_iff.2 ⟨u, hu, rfl⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
