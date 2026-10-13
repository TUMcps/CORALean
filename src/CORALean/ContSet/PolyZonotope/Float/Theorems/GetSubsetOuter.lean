import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

/-!
# `PolyZonotope.getSubset` over-approximates the exact re-parametrization

A point of the exact layer's `getSubset` of the stored set, plus a point of its error box, is a
point of the float `getSubset`: the same factor values and coefficients reach the stored
generators, which differ from the exact ones by at most `getSubsetGDiff` entrywise, and that
difference, scaled by monomials in `[-1, 1]`, lies in the box `generatorError` that was added.
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

theorem PolyZonotope.getSubset_outer (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (cen rad : 𝕋) :
    (Real.PolyZonotope.getSubset (nominal pZ) k (toReal cen) (toReal rad)).construct
        + pZ.err.construct ⊆ (pZ.getSubset k cen rad).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hz⟩ := Real.PolyZonotope.mem_construct_iff.mp hz
  -- the rounding of the generators, scaled by the monomials, lies in the added box
  have hbox : (fun i => ∑ l, (Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen)
        (toReal rad) l i - toReal (pZ.getSubsetGDown k cen rad i l))
          * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l)
      ∈ (PolyZonotope.generatorError (pZ.getSubsetGDiff k cen rad)).construct :=
    PolyZonotope.mem_generatorError_monomial (PolyZonotope.getSubsetG_close pZ k cen rad) ha
  -- the float point at the same coefficients, plus what the rounding and the box add
  refine ⟨fun i => toReal ((pZ.getSubset k cen rad).c i)
      + (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), toReal (pZ.getSubsetGDown k cen rad i l)
          * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l)
      + ∑ j : Fin pZ.q, toReal ((pZ.getSubset k cen rad).GI j i) * β j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
    fun i => (∑ l, (Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l i
        - toReal (pZ.getSubsetGDown k cen rad i l))
        * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l) + e i,
    ?_, ?_⟩
  · -- the sum of the two boxes' points is a point of the interval sum
    intro i
    have h₁ : toReal (pZ.err.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (pZ.err.sup i) := (he i).2
    have h₃ : toReal ((PolyZonotope.generatorError (pZ.getSubsetGDiff k cen rad)).inf i) ≤
          (∑ l, (Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l i
            - toReal (pZ.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l) ∧
        (∑ l, (Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l i
            - toReal (pZ.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l) ≤
          toReal ((PolyZonotope.generatorError (pZ.getSubsetGDiff k cen rad)).sup i) := hbox i
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry]
      linarith [h₃.1]
    · simp only [Entrywise.entry]
      linarith [h₃.2]
  · funext i
    -- the exact point's coordinate, with the stored fields spelt as the exact ones
    have hzi : z i = toReal (pZ.c i)
        + (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)),
          Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l i
            * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l)
        + ∑ j : Fin pZ.q, toReal (pZ.GI j i) * β j := hz i
    -- the stored and the exact generator sums differ by exactly the box's point
    have hsum : (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), toReal (pZ.getSubsetGDown k cen rad i l)
          * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l)
        + (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)),
          (Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l i
            - toReal (pZ.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l)
        = ∑ l : Fin (pZ.h * (pZ.maxExp k + 1)),
          Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l i
            * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    -- spelt out, the coordinate is the exact point's plus the box's
    show toReal (pZ.c i)
        + (∑ l : Fin (pZ.h * (pZ.maxExp k + 1)), toReal (pZ.getSubsetGDown k cen rad i l)
          * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l)
        + (∑ j : Fin pZ.q, toReal (pZ.GI j i) * β j)
        + ((∑ l : Fin (pZ.h * (pZ.maxExp k + 1)),
          (Real.PolyZonotope.getSubsetG (nominal pZ) k (toReal cen) (toReal rad) l i
            - toReal (pZ.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal pZ) k) a l)
          + e i) = z i + e i
    rw [hzi]
    linarith [hsum]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
