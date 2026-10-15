module

public import CORALean.ContSet.ConZonotope.Float.Operations.CubMap
public import CORALean.ContSet.ConZonotope.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.HPolytope.Float.Operations.MemLiftNominalIff
public import CORALean.ContSet.Zonotope.Float.Theorems.CubMapDepCoeff

@[expose] public section

/-!
# `ConZonotope.cubMap` over-approximates the cubic map, over a floating-point scalar

Every point of the operand, box included, is a point of the nominal set of `absorbRounding`
(`absorbRounding_nominal`); its coefficients `β` meet the constraints, and
`Zonotope.cubMapDep_coeff` gives coefficients whose linear block is `β`, so they meet the lifted
constraints. The monomials are unconstrained, so the result is an outer approximation, not the
image.
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

theorem ConZonotope.cubMap_outer (T : Fin m → Fin n → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    Real.PolyZonotope.cubEval (fun i k => toRealMat (T i k)) '' cZ.construct
      ⊆ (cZ.cubMap T).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨β, hβ, hP, hxβ⟩ :=
    ConZonotope.mem_nominalSet_iff.mp (ConZonotope.absorbRounding_nominal cZ hx)
  obtain ⟨γ, hγ, hlin, e, he, heq⟩ := Zonotope.cubMapDep_coeff T
    (⟨cZ.absorbRounding.h, cZ.absorbRounding.c, cZ.absorbRounding.G,
      cZ.absorbRounding.I_error⟩ : Zonotope (Vec 𝕋 n)) β hβ
  -- the lifted constraints read the linear block, which is `β`
  have hdims : Function.Injective fun j : Fin cZ.absorbRounding.h =>
      (Real.Zonotope.cubIdx (cZ.absorbRounding.h + 1) (cZ.absorbRounding.h + 1)
        (cZ.absorbRounding.h + 1)).symm ((0, 0), j.succ) :=
    fun a b hab => Fin.succ_injective _ (by simpa using hab)
  have hP' : γ ∈ ((cZ.cubMap T).P).nominal.construct := by
    show γ ∈ (cZ.absorbRounding.P.lift_ fun j : Fin cZ.absorbRounding.h =>
      (Real.Zonotope.cubIdx (cZ.absorbRounding.h + 1) (cZ.absorbRounding.h + 1)
        (cZ.absorbRounding.h + 1)).symm ((0, 0), j.succ)).nominal.construct
    refine (HPolytope.mem_lift_nominal_iff cZ.absorbRounding.P hdims).mpr ?_
    show (fun j => γ _) ∈ cZ.absorbRounding.P.nominal.construct
    have : (fun j : Fin cZ.absorbRounding.h => γ ((Real.Zonotope.cubIdx (cZ.absorbRounding.h + 1)
        (cZ.absorbRounding.h + 1) (cZ.absorbRounding.h + 1)).symm
        ((0, 0), j.succ))) = β := funext hlin
    rw [this]
    exact hP
  -- the stored nominal point at `γ`, and the shortfall in the box
  refine ⟨_, ConZonotope.mem_nominalSet_iff.mpr ⟨γ, hγ, hP', fun _ => rfl⟩, e, he, ?_⟩
  have hx' : x = toRealVec cZ.absorbRounding.c + ∑ j, β j • toRealVec (cZ.absorbRounding.G j) := by
    funext i
    simp [hxβ i, Finset.sum_apply, mul_comm, toRealVec]
  rw [hx', heq]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
