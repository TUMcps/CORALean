module

public import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial

@[expose] public section

/-!
# The constraints of the float `ConPolyZono.getSubset`

Wherever the exact layer's `getSubset` of the stored set meets its constraint at a factor vector
in `[-1, 1]ᵖ`, the float `getSubset` meets its own: what `A μ` loses to the rounding of the
re-parametrized constraint matrix, scaled by monomials in `[-1, 1]`, is a point of the box `b`
was widened by.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The widened `b` holds wherever the exact constraint system does. -/
theorem ConPolyZono.getSubset_satisfies (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (k : Fin cPZ.p) (cen rad : 𝕋)
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
        (cPZ.getSubset k cen rad).R a) i
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
    have h2 : Real.PolyZonotope.monomial (cPZ.getSubset k cen rad).R a l
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
