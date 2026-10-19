module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.GetSubset
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Real.Operations.GetSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetGClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial

@[expose] public section

/-!
# The rows of the float `PolyLevelSet.getSubset`

Wherever the exact layer's `getSubset` of the read-back rows (`nominalCore`) meets every equation
within its slack at a point of `[-1, 1]ⁿ`, the float `getSubset` meets its own: what the row loses
to the rounding of the re-parametrized coefficients, scaled by monomials in `[-1, 1]`, is at most
the row radius the slack was widened by.

## Inputs
* `P` – polynomial level set
* `k` – variable index
* `cen` – new center of the variable
* `rad` – new radius of the variable
* `a` – real point

## Hypotheses
* `hP` – all rows are equations
* `ha` – `a` lies in the unit box
* `hdom` – `a` lies in the box
* `hsat` – exact `getSubset` rows hold within their slacks

## Conclusion
* `a` lies in the float `getSubset`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The widened slack holds wherever the exact re-parametrized rows are within the old one, at a
point of the box. -/
theorem PolyLevelSet.mem_getSubset_of_real (P : PolyLevelSet 𝕋 n) (hP : ∀ i, P.op i = .eq)
    (k : Fin n) (cen rad : 𝕋) (a : Fin n → ℝ) (ha : ∀ k, |a k| ≤ 1) (hdom : a ∈ P.dom.construct)
    (hsat : ∀ i, |(P.nominalCore.getSubset k (toReal cen) (toReal rad)).eval a i|
      ≤ |toReal (P.b_error i)|) : -- --- CONCL ---
    a ∈ (P.getSubset k cen rad).construct := by -- --- PROOF ---
  -- the exact generators, the stored (rounded down) ones, and the monomials, named once
  set G := Real.PolyZonotope.getSubsetG (nominal P.lhs) k (toReal cen) (toReal rad)
  set Gd := P.lhs.getSubsetGDown k cen rad
  set mon := Real.PolyZonotope.monomial (Real.PolyZonotope.getSubsetE (nominal P.lhs) k) a
  -- what rounding `A` costs, scaled by the monomials, a point of the box
  have hd : (fun i => ∑ l, (toReal (Gd i l) - G l i) * mon l)
      ∈ (PolyZonotope.generatorError (P.lhs.getSubsetGDiff k cen rad)).construct :=
    PolyZonotope.mem_generatorError_monomial
      (fun i l => by
        rw [abs_sub_comm]
        exact PolyZonotope.getSubsetG_close P.lhs k cen rad i l) ha
  refine (PolyLevelSet.mem_construct_iff_of_eq (P := P.getSubset k cen rad) hP).mpr
    ⟨hdom, fun i => ?_⟩
  have hi := hd i
  -- and the stored row is the exact one plus that point
  have heq : ((toRealMat (P.getSubset k cen rad).A) *ᵥ Real.PolyZonotope.monomial
        (P.getSubset k cen rad).R a) i
      = ((P.nominalCore.getSubset k (toReal cen) (toReal rad)).A
        *ᵥ Real.PolyZonotope.monomial (P.lhs.getSubset k cen rad).E a) i
        + ∑ l, (toReal (Gd i l) - G l i) * mon l := by
    -- entrywise, one sum over the new columns on each side
    simp only [Matrix.mulVec, dotProduct, toRealMat]
    erw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    -- the fields read the same on both sides
    have h1 : (P.nominalCore.getSubset k (toReal cen) (toReal rad)).A i l = G l i := rfl
    have h2 : Real.PolyZonotope.monomial (P.getSubset k cen rad).R a l = mon l := rfl
    have h4 : toReal ((P.getSubset k cen rad).A i l) = toReal (Gd i l) := rfl
    erw [h1, h2, h4]
    ring
  -- the slack grew by the radius bounding that point
  have hr : toReal ((PolyZonotope.generatorError
        (P.lhs.getSubsetGDiff k cen rad)).inf i) ≤ _ ∧ _ ≤ toReal
        ((PolyZonotope.generatorError (P.lhs.getSubsetGDiff k cen rad)).sup i) := hi
  simp only [PolyZonotope.generatorError, Interval.symmetric, Entrywise.entry, Pi.neg_apply,
    toReal_neg'] at hr
  have hu := add_le_addUp (absolute (P.b_error i)) (radius (P.lhs.getSubsetGDiff k cen rad) i)
  rw [toReal_absolute] at hu
  have hs : |((P.nominalCore.getSubset k (toReal cen) (toReal rad)).A
        *ᵥ Real.PolyZonotope.monomial (P.lhs.getSubset k cen rad).E a) i - toReal (P.b i)|
      ≤ |toReal (P.b_error i)| := hsat i
  show |(toRealMat (P.getSubset k cen rad).A *ᵥ Real.PolyZonotope.monomial
      (P.getSubset k cen rad).R a) i - toReal (P.b i)| ≤ |toReal (addUp
      (absolute (P.b_error i)) (radius (P.lhs.getSubsetGDiff k cen rad) i))|
  rw [heq]
  rw [abs_le] at hs ⊢
  have hu' := le_abs_self (toReal (addUp (absolute (P.b_error i))
    (radius (P.lhs.getSubsetGDiff k cen rad) i)))
  constructor <;> linarith [hs.1, hs.2, hr.1, hr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
