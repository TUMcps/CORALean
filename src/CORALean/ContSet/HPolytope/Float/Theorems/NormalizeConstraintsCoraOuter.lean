module

public import CORALean.ContSet.HPolytope.Float.Operations.NormalizeConstraintsCora
public import CORALean.ContSet.HPolytope.Float.Theorems.ScaleRowsDivOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.ErrFreeOfIsErrFree

@[expose] public section

/-!
# `HPolytope.normalizeConstraintsCora` keeps every point of the polytope inside the domain

The divisors are positive for an inequality row and certified negative or positive for an equality
row, so `scaleRowsDiv_outer` applies to the polytope with its error box folded in.

## Inputs
* `P` – H-polytope
* `dom` – domain interval

## Hypotheses
* none

## Conclusion
* inside `dom`, the normalized polytope contains the original
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The inequality divisor is positive. -/
private theorem HPolytope.aux_normDivisorA_pos (b : 𝕋) : -- --- CONCL ---
    0 < toReal (HPolytope.step_normDivisorA b) := by -- --- PROOF ---
  by_cases h : ltStrict zero (absolute b) = true
  · -- certified positive: the divisor is `|b|`
    simp only [HPolytope.step_normDivisorA, h, if_true]
    have := toReal_lt_of_ltStrict h
    rwa [toReal_zero] at this
  · -- otherwise the divisor is one
    simp only [HPolytope.step_normDivisorA, h, Bool.false_eq_true, if_false]
    rw [toReal_one]
    exact one_pos

/-- The equality divisor is certified negative or positive. -/
private theorem HPolytope.aux_normDivisorE (b : 𝕋) : -- --- CONCL ---
    ltStrict (HPolytope.step_normDivisorE b) zero = true
      ∨ 0 < toReal (HPolytope.step_normDivisorE b) := by -- --- PROOF ---
  by_cases h1 : ltStrict zero b = true
  · -- certified positive
    refine Or.inr ?_
    simp only [HPolytope.step_normDivisorE, h1, if_true]
    have := toReal_lt_of_ltStrict h1
    rwa [toReal_zero] at this
  · by_cases h2 : ltStrict b zero = true
    · -- certified negative
      refine Or.inl ?_
      simp only [HPolytope.step_normDivisorE, h1, h2, Bool.false_eq_true, if_false, if_true]
    · -- neither: the divisor is one
      refine Or.inr ?_
      simp only [HPolytope.step_normDivisorE, h1, h2, Bool.false_eq_true, if_false]
      rw [toReal_one]
      exact one_pos


-- =======================================  MAIN THEOREM  ======================================= --

/-- Normalizing keeps every point of the polytope that lies in the domain box. -/
theorem HPolytope.normalizeConstraintsCora_outer (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    P.toSet ∩ dom.toSet ⊆ (P.normalizeConstraintsCora dom).toSet ∩ dom.toSet := by -- --- PROOF ---
  -- the rows as stored when the box is certified empty, else with the box folded in
  have hfree : (if P.isErrFree then P else P.absorbRounding).IsErrFree := by
    split <;> rename_i h
    exacts [HPolytope.errFree_of_isErrFree h, HPolytope.isErrFree_of_origin rfl rfl rfl]
  intro x hx
  refine HPolytope.scaleRowsDiv_outer (if P.isErrFree then P else P.absorbRounding) hfree _ _
    (fun _ => HPolytope.aux_normDivisorA_pos _) (fun _ => HPolytope.aux_normDivisorE _) dom
    ⟨?_, hx.2⟩
  -- the point stays in the polytope with the box folded in
  split
  exacts [hx.1, HPolytope.absorbRounding_outer P hx.1]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
