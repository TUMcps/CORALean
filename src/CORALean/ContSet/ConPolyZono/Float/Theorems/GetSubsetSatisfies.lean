module

public import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# The constraints of the float `ConPolyZono.getSubset`

Wherever the exact layer's `getSubset` of the stored set (`nominalCore`) meets its rows within
their slack at a factor vector in `[-1, 1]ᵖ`, the float `getSubset` meets its own: what `A μ`
loses to the rounding of the re-parametrized constraint matrix, scaled by monomials in `[-1, 1]`,
is at most the row radius the slack was widened by.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The widened slack holds wherever the exact rows are within the old one. -/
theorem ConPolyZono.getSubset_satisfies (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (k : Fin cPZ.p) (cen rad : 𝕋)
    (a : Fin cPZ.p → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (hsat : ∀ i, |((Real.ConPolyZono.getSubset cPZ.nominalCore k (toReal cen) (toReal rad)).cons.A
        *ᵥ Real.PolyZonotope.monomial (cPZ.consPolyZonotope.getSubset k cen rad).E a) i
        - toReal (cPZ.cons.b i)| ≤ |toReal (cPZ.cons.b_error i)|) : -- --- STMT ---
    a ∈ (cPZ.getSubset k cen rad).cons.construct := by -- --- PROOF ---
  -- the exact generators, the stored (rounded down) ones, and the monomials, named once
  set G := Real.PolyZonotope.getSubsetG (nominal cPZ.consPolyZonotope) k (toReal cen) (toReal rad)
  set Gd := cPZ.consPolyZonotope.getSubsetGDown k cen rad
  set mon := Real.PolyZonotope.monomial
    (Real.PolyZonotope.getSubsetE (nominal cPZ.consPolyZonotope) k) a
  -- what rounding `A` costs, scaled by the monomials, a point of the box
  have hd : (fun i => ∑ l, (toReal (Gd i l) - G l i) * mon l)
      ∈ (PolyZonotope.generatorError (cPZ.consPolyZonotope.getSubsetGDiff k cen rad)).construct :=
    PolyZonotope.mem_generatorError_monomial
      (fun i l => by
        rw [abs_sub_comm]
        exact PolyZonotope.getSubsetG_close cPZ.consPolyZonotope k cen rad i l) ha
  refine (PolyLevelSet.mem_construct_iff_of_eq (cPZ.getSubset k cen rad).cons_eq).mpr fun i => ?_
  have hi := hd i
  -- and the stored row is the exact one plus that point
  have heq : ((toRealMat (cPZ.getSubset k cen rad).cons.A) *ᵥ Real.PolyZonotope.monomial
        (cPZ.getSubset k cen rad).cons.R a) i
      = ((Real.ConPolyZono.getSubset cPZ.nominalCore k (toReal cen) (toReal rad)).cons.A
        *ᵥ Real.PolyZonotope.monomial (cPZ.consPolyZonotope.getSubset k cen rad).E a) i
        + ∑ l, (toReal (Gd i l) - G l i) * mon l := by
    -- entrywise, one sum over the new columns on each side
    simp only [Matrix.mulVec, dotProduct, toRealMat]
    erw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    -- the fields read the same on both sides
    have h1 : (cPZ.nominalCore.getSubset k (toReal cen) (toReal rad)).cons.A i l = G l i := rfl
    have h2 : Real.PolyZonotope.monomial (cPZ.getSubset k cen rad).cons.R a l = mon l := rfl
    have h4 : toReal ((cPZ.getSubset k cen rad).cons.A i l) = toReal (Gd i l) := rfl
    erw [h1, h2, h4]
    ring
  -- the slack grew by the radius bounding that point
  have hr : toReal ((PolyZonotope.generatorError
        (cPZ.consPolyZonotope.getSubsetGDiff k cen rad)).inf i) ≤ _ ∧ _ ≤ toReal
        ((PolyZonotope.generatorError (cPZ.consPolyZonotope.getSubsetGDiff k cen rad)).sup i) := hi
  simp only [PolyZonotope.generatorError, Interval.symmetric, Entrywise.entry, Pi.neg_apply,
    toReal_neg'] at hr
  have hu := add_le_addUp (absolute (cPZ.cons.b_error i))
    (radius (cPZ.consPolyZonotope.getSubsetGDiff k cen rad) i)
  rw [toReal_absolute] at hu
  have hs := hsat i
  show |(toRealMat (cPZ.getSubset k cen rad).cons.A *ᵥ Real.PolyZonotope.monomial
      (cPZ.getSubset k cen rad).cons.R a) i - toReal (cPZ.cons.b i)| ≤ |toReal (addUp
      (absolute (cPZ.cons.b_error i)) (radius (cPZ.consPolyZonotope.getSubsetGDiff k cen rad) i))|
  rw [heq]
  rw [abs_le] at hs ⊢
  have hu' := le_abs_self (toReal (addUp (absolute (cPZ.cons.b_error i))
    (radius (cPZ.consPolyZonotope.getSubsetGDiff k cen rad) i)))
  constructor <;> linarith [hs.1, hs.2, hr.1, hr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
