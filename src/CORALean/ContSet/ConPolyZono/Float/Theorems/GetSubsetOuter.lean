import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial

/-!
# `ConPolyZono.getSubset` over-approximates the exact re-parametrization

A point of the exact layer's `getSubset` of the stored set, plus a point of its error box, is a
point of the float `getSubset`. The generators are as for `PolyZonotope.getSubset`: the rounding
they cost, scaled by monomials in `[-1, 1]`, lies in the box added to `err`. The constraint matrix
is rounded the same way, and the same bound, scaled by the same monomials, moves the exact
constraint value into the widened `b`: what `A μ` loses to the rounding of `A` is a point of the
box `b` was widened by, so the stored system holds wherever the exact one does.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The widened `b` holds wherever the exact constraint system does. -/
theorem ConPolyZono.aux_getSubset_satisfies (cPZ : ConPolyZono 𝕋 n) (k : Fin cPZ.p) (cen rad : 𝕋)
    (a : Fin cPZ.p → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (hsat : (Real.ConPolyZono.getSubset (nominal cPZ) k (toReal cen) (toReal rad)).satisfies a) :
    (cPZ.getSubset k cen rad).satisfies a := by -- --- PROOF ---
  -- the exact constraint value, a point of `b`
  have hy : (Real.ConPolyZono.getSubset (nominal cPZ) k (toReal cen) (toReal rad)).A
      *ᵥ Real.PolyZonotope.monomial (cPZ.consPolyZonotope.getSubset k cen rad).E a
      ∈ cPZ.b.construct := hsat
  -- what rounding `A` costs, scaled by the monomials, a point of the box
  have hd : (fun i => ∑ l, (toReal (cPZ.consPolyZonotope.getSubsetGDown k cen rad i l)
        - Real.PolyZonotope.getSubsetG (nominal cPZ.consPolyZonotope) k (toReal cen) (toReal rad)
            l i) * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.consPolyZonotope) k) a l)
      ∈ (PolyZonotope.generatorError (cPZ.consPolyZonotope.getSubsetGDiff k cen rad)).construct :=
    PolyZonotope.mem_generatorError_monomial
      (fun i l => by
        rw [abs_sub_comm]
        exact PolyZonotope.getSubsetG_close cPZ.consPolyZonotope k cen rad i l) ha
  -- the exact value plus that point is a point of the widened `b`
  have hmem := Interval.plus_outer _ _ ⟨_, hy, _, hd, rfl⟩
  intro i
  have hi := hmem i
  -- and is what the stored matrix gives
  have heq : ((toRealMat (cPZ.getSubset k cen rad).A) *ᵥ Real.PolyZonotope.monomial
        (cPZ.getSubset k cen rad).EC a) i
      = ((Real.ConPolyZono.getSubset (nominal cPZ) k (toReal cen) (toReal rad)).A
        *ᵥ Real.PolyZonotope.monomial (cPZ.consPolyZonotope.getSubset k cen rad).E a) i
        + ∑ l, (toReal (cPZ.consPolyZonotope.getSubsetGDown k cen rad i l)
          - Real.PolyZonotope.getSubsetG (nominal cPZ.consPolyZonotope) k (toReal cen)
              (toReal rad) l i)
          * Real.PolyZonotope.monomial
            (Real.PolyZonotope.getSubsetE (nominal cPZ.consPolyZonotope) k) a l := by
    -- entrywise, one sum over the new columns on each side
    simp only [Matrix.mulVec, dotProduct, toRealMat]
    erw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    -- the fields read the same on both sides
    have h1 : ((nominal cPZ).getSubset k (toReal cen) (toReal rad)).A i l
        = Real.PolyZonotope.getSubsetG (nominal cPZ.consPolyZonotope) k (toReal cen) (toReal rad)
          l i := rfl
    have h2 : Real.PolyZonotope.monomial (cPZ.getSubset k cen rad).EC a l
        = Real.PolyZonotope.monomial
          (Real.PolyZonotope.getSubsetE (nominal cPZ.consPolyZonotope) k) a l := rfl
    have h3 : Real.PolyZonotope.monomial (cPZ.consPolyZonotope.getSubset k cen rad).E a l
        = Real.PolyZonotope.monomial
          (Real.PolyZonotope.getSubsetE (nominal cPZ.consPolyZonotope) k) a l := rfl
    have h4 : toReal ((cPZ.getSubset k cen rad).A i l)
        = toReal (cPZ.consPolyZonotope.getSubsetGDown k cen rad i l) := rfl
    erw [h1, h2, h3, h4]
    ring
  show _ ≤ _ ∧ _ ≤ _
  rw [heq]
  exact hi


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.getSubset_outer (cPZ : ConPolyZono 𝕋 n) (k : Fin cPZ.p) (cen rad : 𝕋) :
    (Real.ConPolyZono.getSubset (nominal cPZ) k (toReal cen) (toReal rad)).construct
        + cPZ.err.construct ⊆ (cPZ.getSubset k cen rad).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hsat, hz⟩ := Real.ConPolyZono.mem_construct_iff.mp hz
  -- the rounding of the generators, scaled by the monomials, lies in the added box
  have hbox : (fun i => ∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k
        (toReal cen) (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
          * Real.PolyZonotope.monomial
            (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
      ∈ (PolyZonotope.generatorError (cPZ.toPolyZonotope.getSubsetGDiff k cen rad)).construct :=
    PolyZonotope.mem_generatorError_monomial
      (PolyZonotope.getSubsetG_close cPZ.toPolyZonotope k cen rad) ha
  -- the float point at the same factors and coefficients, plus what the rounding and the box add
  refine ⟨fun i => toReal ((cPZ.getSubset k cen rad).c i)
      + (∑ l, toReal ((cPZ.getSubset k cen rad).G l i)
          * Real.PolyZonotope.monomial (cPZ.getSubset k cen rad).E a l)
      + ∑ j : Fin cPZ.q, toReal ((cPZ.getSubset k cen rad).GI j i) * β j,
    ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ,
      ConPolyZono.aux_getSubset_satisfies cPZ k cen rad a ha hsat, fun _ => rfl⟩,
    fun i => (∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
        (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
        * Real.PolyZonotope.monomial
          (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l) + e i,
    ?_, ?_⟩
  · -- the sum of the two boxes' points is a point of the interval sum
    intro i
    have h₁ : toReal (cPZ.toPolyZonotope.err.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (cPZ.toPolyZonotope.err.sup i) := (he i).2
    -- the generator rounding's point, within its own box
    have h₃ : toReal ((PolyZonotope.generatorError
          (cPZ.toPolyZonotope.getSubsetGDiff k cen rad)).inf i) ≤
          (∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l) ∧
        (∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l) ≤
          toReal ((PolyZonotope.generatorError
            (cPZ.toPolyZonotope.getSubsetGDiff k cen rad)).sup i) := hbox i
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry]
      linarith [h₃.1]
    · simp only [Entrywise.entry]
      linarith [h₃.2]
  · funext i
    -- the exact point's coordinate, with the stored fields spelt as the exact ones
    have hzi : z i = toReal (cPZ.c i)
        + (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen) (toReal rad) l i
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
        + ∑ j : Fin cPZ.q, toReal (cPZ.GI j i) * β j := hz i
    -- the stored and the exact generator sums differ by exactly the box's point
    have hsum : (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l)
          * Real.PolyZonotope.monomial
            (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
        + (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
        = ∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen) (toReal rad) l i
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    -- spelt out, the coordinate is the exact point's plus the box's
    show toReal (cPZ.c i)
        + (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l)
          * Real.PolyZonotope.monomial
            (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
        + (∑ j : Fin cPZ.q, toReal (cPZ.GI j i) * β j)
        + ((∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
          + e i) = z i + e i
    rw [hzi]
    linarith [hsum]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
