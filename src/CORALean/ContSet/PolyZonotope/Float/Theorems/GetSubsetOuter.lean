module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `PolyZonotope.getSubset` over-approximates the exact re-parametrization

A point of the exact layer's `getSubset` of the stored set, plus a point of its error box, is a
point of the float `getSubset`: the same factor values and coefficients reach the stored
generators, which differ from the exact ones by at most `getSubsetGDiff` entrywise, and that
difference, scaled by monomials in `[-1, 1]`, lies in the box `generatorError` that was added.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index
* `cen` – subinterval center
* `rad` – subinterval radius

## Hypotheses
* none

## Conclusion
* the exact subset plus the error box lies in the result
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

theorem PolyZonotope.getSubset_outer (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p)
    (cen rad : 𝕋) : -- --- CONCL ---
    (Real.PolyZonotope.getSubset (nominal pZ) k (toReal cen) (toReal rad)).construct
        + pZ.I_error.construct ⊆ (pZ.getSubset k cen rad).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := Real.PolyZonotope.mem_construct_iff.mp hz
  -- the exact generators, the stored (rounded down) ones and the monomials, named once
  set G := Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad)
  set Gd : Fin n → Fin (pZ.h * (pZ.maxExp k + 1)) → 𝕋 := pZ.getSubsetGDown k cen rad
  set mon := Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a
  -- the rounding of the generators, scaled by the monomials, lies in the added box
  set err : Fin n → ℝ := fun i =>
    ∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), (G l i - toReal (Gd i l)) * mon l with herr
  have hbox : err ∈ (PolyZonotope.generatorError (pZ.getSubsetGDiff k cen rad)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.getSubsetG_close pZ k cen rad) ha
  -- the float point at the same coefficients, plus what the rounding and the box add
  refine ⟨fun i => toReal ((pZ.getSubset k cen rad).c i)
      + (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), toReal (Gd i l) * mon l)
      + ∑ j : Fin pZ.q, toReal ((pZ.getSubset k cen rad).GI j i) * β j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
    fun i => err i + e i, ?_, ?_⟩
  · -- the sum of the two boxes' points is a point of the interval sum
    intro i
    have h₁ : toReal (pZ.I_error.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (pZ.I_error.sup i) := (he i).2
    have h₃ : toReal ((PolyZonotope.generatorError (pZ.getSubsetGDiff k cen rad)).inf i) ≤ err i ∧
        err i ≤ toReal ((PolyZonotope.generatorError (pZ.getSubsetGDiff k cen rad)).sup i) :=
      hbox i
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry]
      linarith [h₃.1]
    · simp only [Entrywise.entry]
      linarith [h₃.2]
  · funext i
    -- the exact point's coordinate, with the stored fields spelt as the exact ones
    have hzi : z i = toReal (pZ.c i) + (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), G l i * mon l)
        + ∑ j : Fin pZ.q, toReal (pZ.GI j i) * β j := hz i
    -- the stored and the exact generator sums differ by exactly the box's point
    have hsum : (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), toReal (Gd i l) * mon l) + err i
        = ∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), G l i * mon l := by
      simp only [herr]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    -- spelt out, the coordinate is the exact point's plus the box's
    show toReal (pZ.c i) + (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), toReal (Gd i l) * mon l)
        + (∑ j : Fin pZ.q, toReal (pZ.GI j i) * β j) + (err i + e i) = z i + e i
    rw [hzi]
    linarith [hsum]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
