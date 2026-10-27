module

public import CORALean.ContSet.Zonotope.Real.Operations.Aligned
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# (max-in) with `W`'s own halfspaces does not stay inside `EW`

[1, Prop. 2] as printed builds (max-in) from the H-representation `(H, h)` of `W`
and concludes `Z(Z, EW) ⊆ EW`. In one dimension with `W = [-1, 1]`
(`H = (1, -1)ᵀ`, `h = (1, 1)`), `E = ½` and `Z = [-1, 1]`, the maximizer of (max-in)
with [1]'s weights `dᵢ = ‖gᵢ‖` is `α = 1`, `c = 0`: the aligned zonotope is `[-1, 1]`,
and `EW = [-½, ½]` does not contain it. With `EW`'s own description `(2H, h)` the
same problem gives `α = ½`, which `aligned_subset_of_maxIn` covers.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a maximizer exists whose aligned zonotope is not inside `EW`

## References

* [1] [L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for
      uncertain linear systems". IEEE Control Systems Letters,
      2022.](../../../../../../references/2022/yang-lcss-zonotopic-underapproximation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] as printed: a maximizer of (max-in) over `W`'s halfspaces whose aligned
zonotope is not inside `EW`. -/
theorem Zonotope.aligned_subset_of_maxIn_counterexample : -- --- CONCL ---
    ∃ (Z : Zonotope (Vec ℝ 1)) (H : Mat ℝ 2 1) (h : Vec ℝ 2) (E : Mat ℝ 1 1) (c : Vec ℝ 1)
      (a : Fin Z.h → ℝ),
      (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧ (∀ l, (H *ᵥ c) l + ∑ i, |(H *ᵥ Z.G i) l| * a i ≤ h l) ∧
      (∀ (c' : Vec ℝ 1) (a' : Fin Z.h → ℝ), (∀ i, 0 ≤ a' i ∧ a' i ≤ 1) →
        (∀ l, (H *ᵥ c') l + ∑ i, |(H *ᵥ Z.G i) l| * a' i ≤ h l) →
        ∑ i, ‖Z.G i‖ * Real.log (a' i) ≤ ∑ i, ‖Z.G i‖ * Real.log (a i)) ∧
      ¬ (Z.aligned c a).construct ⊆ (E *ᵥ ·) '' {w | ∀ l, (H *ᵥ w) l ≤ h l} := by -- --- PROOF ---
  refine ⟨⟨1, 0, fun _ _ => 1⟩, !![1; -1], ![1, 1], !![1 / 2], 0, fun _ => 1,
    fun _ => ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_⟩
  -- feasible: `±0 + 1 ≤ 1`
  · intro l
    fin_cases l <;> simp [Matrix.mulVec, dotProduct]
  -- maximal: every feasible `α' ≤ 1` has `log α' ≤ 0 = log 1`
  · intro c' a' ha' _
    simp only [Real.log_one, mul_zero, Finset.sum_const_zero]
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (Real.log_nonpos (ha' i).1 (ha' i).2)
  -- `1 ∈ [-1, 1]`, while `1 = w / 2` needs `w = 2 ∉ W`
  · intro hsub
    have hmem : ((fun _ => 1 : Fin 1 → ℝ) : Vec ℝ 1) ∈ (Zonotope.aligned
        (⟨1, 0, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1)) 0 (fun _ => (1 : ℝ))).construct := by
      refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
      funext i
      simp [Zonotope.aligned]
    obtain ⟨w, hw, hEw⟩ := hsub hmem
    have h1 := congrFun hEw 0
    have h2 := hw 0
    simp [Matrix.mulVec, dotProduct] at h1 h2
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
