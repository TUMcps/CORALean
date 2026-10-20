module

public import CORALean.ContSet.Taylm.Real.Operations.ProdBounds
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# The product of intervals contains every product

Entry by entry, each factor in its interval: `mul_between_corners` at each step of the fold.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the product of intervals contains every product of members
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.prodBounds_mem : -- --- CONCL ---
    ∀ (L : List (Interval ℝ)) (x : List ℝ), L.length = x.length →
    (∀ i (h₁ : i < L.length) (h₂ : i < x.length), L[i].inf ≤ x[i] ∧ x[i] ≤ L[i].sup) →
    (Taylm.prodBounds L).inf ≤ x.prod ∧ x.prod ≤ (Taylm.prodBounds L).sup
  | [], [], _, _ => by simp [Taylm.prodBounds]
  | a :: L, y :: x, hl, hm => by
    have h0 := hm 0 (by simp) (by simp)
    have ih := Taylm.prodBounds_mem L x (by simpa using hl) fun i h₁ h₂ =>
      hm (i + 1) (by simpa using h₁) (by simpa using h₂)
    simp only [List.getElem_cons_zero] at h0
    simp only [Taylm.prodBounds, List.prod_cons]
    exact Interval.mul_between_corners h0.1 h0.2 ih.1 ih.2
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
