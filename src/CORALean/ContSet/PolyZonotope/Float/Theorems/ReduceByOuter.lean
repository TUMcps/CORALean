module

public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByPoint

@[expose] public section

/-!
# `reduceBy` over-approximates, dropping a chosen pair of blocks

The error box is untouched, so `mono_subset` reduces this to the nominal part.
The point of the set is a point of the reduced one (`reduceBy_point`).

## Inputs
* `pZ` – polynomial zonotope
* `partD` – split of the dependent generators
* `partI` – split of the independent generators

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem PolyZonotope.aux_reduceBy_nominal (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) :
    nominalSet pZ ⊆ nominalSet (pZ.reduceBy partD partI) := by
  intro x hx'
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx'
  obtain ⟨β', hβ', hpt⟩ := PolyZonotope.reduceBy_point pZ partD partI ha hβ
  exact PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β', ha, hβ', fun i => (hx i).trans (hpt i)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceBy_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) :
    pZ.toSet ⊆ (pZ.reduceBy partD partI).toSet :=
  mono_subset (PolyZonotope.aux_reduceBy_nominal pZ partD partI) (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
