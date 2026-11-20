module

public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriCoeff
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbRoundingIfAnyNominal
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Zonotope.quadMapTri` over-approximates the quadratic map, over a floating-point scalar

The operand is the set itself if its box is zero, else with the box made into generators
(`absorbRoundingIfAny_nominal`); a point of `Z` is a point of the operand (`quadMapTri_coeff`).

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the quadratic image of `Z` is contained in the computed zonotope
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `{xᵀQ⁽ⁱ⁾x | x ∈ Z} ⊆ Z.quadMapTri Q`. -/
theorem Zonotope.quadMapTri_outer (Q : Fin m → Mat 𝕋 n n)
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' Z.toSet
      ⊆ (Z.quadMapTri Q).toSet := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the point as a combination of the operand's generators, its image in the stored result
  obtain ⟨β, hβ, hxβ⟩ := Zonotope.mem_nominalSet_iff.mp (Zonotope.absorbRoundingIfAny_nominal Z hx)
  obtain ⟨γ, hγ, e, he, heq⟩ :=
    Zonotope.quadMapTri_coeff Q Z.absorbRoundingIfAny _ rfl β hβ
  refine ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨γ, hγ, fun _ => rfl⟩, e, he, ?_⟩
  have hx' : x = toRealVec Z.absorbRoundingIfAny.c
      + ∑ j, β j • toRealVec (Z.absorbRoundingIfAny.G j) := by
    funext i
    simp [hxβ i, Finset.sum_apply, mul_comm, toRealVec]
  rw [hx', heq]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
