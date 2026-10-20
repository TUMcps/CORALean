module

public import CORALean.ContSet.Zonotope.Float.Operations.CubMap
public import CORALean.ContSet.Zonotope.Float.Theorems.CubMapDepCoeff
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `Zonotope.cubMap` over-approximates the cubic map, over a floating-point scalar

Every point of the operand, box included, is a point of the nominal set of `absorbRounding`
(`absorbRounding_nominal`), whose cubic image is held by `cubMapDep` (`cubMapDep_coeff`). Outer
only: the monomials `β_k β_j β_c` of the factors are tied to each other, and a zonotope frees them.

## Inputs
* `T` – cubic tensor
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* cubic image is contained in the computed zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cubMap_outer (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Real.PolyZonotope.cubEval (fun i k => toRealMat (T i k)) '' Z.construct
      ⊆ (Z.cubMap T).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨p, hp, hxp⟩ := Zonotope.mem_nominalSet_iff.mp (Zonotope.absorbRounding_nominal Z hx)
  obtain ⟨γ, hγ, -, e, he, heq⟩ := Zonotope.cubMapDep_coeff T Z.absorbRounding p hp
  refine ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨γ, hγ, fun _ => rfl⟩, e, he, ?_⟩
  have hx' : x = toRealVec Z.absorbRounding.c + ∑ j, p j • toRealVec (Z.absorbRounding.G j) := by
    funext i
    simp [hxp i, Finset.sum_apply, mul_comm, toRealVec]
  rw [hx', heq]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
