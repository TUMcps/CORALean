module

public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriCoeff
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Zonotope.quadMapTri` over-approximates the quadratic map, over a floating-point scalar

The operand is the set itself if its box is zero, else with the box made into generators
(`absorbRounding_nominal`); a point of `Z` is a point of the operand (`quadMapTri_coeff`).

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the quadratic image of `Z` is contained in the computed zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A zero box (`sup ≤ 0 ≤ inf`) adds nothing, so the points of the set are those of its nominal
part; otherwise the box has been made into generators. -/
private theorem Zonotope.aux_quadMapTri_operand (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Z.toSet ⊆ nominalSet (Zonotope.step_quadMapTriOperand Z) := by -- --- PROOF ---
  unfold Zonotope.step_quadMapTriOperand
  split_ifs with h
  · rintro _ ⟨z, hz, e, he, rfl⟩
    have h0 : e = 0 := by
      funext i
      have h1 := toReal_le_of_le (decide_eq_true_iff.mp h i).1
      have h2 := toReal_le_of_le (decide_eq_true_iff.mp h i).2
      rw [toReal_zero] at h1 h2
      exact le_antisymm (le_trans (he i).2 h1) (le_trans h2 (he i).1)
    simpa [h0] using hz
  · exact Zonotope.absorbRounding_nominal Z


-- =======================================  MAIN THEOREM  ======================================= --

/-- `{xᵀQ⁽ⁱ⁾x | x ∈ Z} ⊆ Z.quadMapTri Q`. -/
theorem Zonotope.quadMapTri_outer (Q : Fin m → Mat 𝕋 n n)
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' Z.toSet
      ⊆ (Z.quadMapTri Q).toSet := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the point as a combination of the operand's generators, its image in the stored result
  obtain ⟨β, hβ, hxβ⟩ := Zonotope.mem_nominalSet_iff.mp (Zonotope.aux_quadMapTri_operand Z hx)
  obtain ⟨γ, hγ, e, he, heq⟩ :=
    Zonotope.quadMapTri_coeff Q (Zonotope.step_quadMapTriOperand Z) _ rfl β hβ
  refine ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨γ, hγ, fun _ => rfl⟩, e, he, ?_⟩
  have hx' : x = toRealVec (Zonotope.step_quadMapTriOperand Z).c
      + ∑ j, β j • toRealVec ((Zonotope.step_quadMapTriOperand Z).G j) := by
    funext i
    simp [hxβ i, Finset.sum_apply, mul_comm, toRealVec]
  rw [hx', heq]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
