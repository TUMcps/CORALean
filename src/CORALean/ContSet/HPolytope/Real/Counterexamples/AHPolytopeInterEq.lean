module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `[1, Eq. 7]` fails without a range row

In `ℝ¹`: `X₁ = [-1, 1]`, and `X₂ = {5}`, written `5 + 0 · [-1, 1]`, whose map `X₂ = 0` has
Moore-Penrose inverse `0`. The intersection is empty, yet `P_∩` as `[1, Eq. 7]` builds it —
read with `H₂` on the `w` block and the offset `x̄₁` it drops, so that it type-checks — is
all of `[-1, 1] × [-1, 1]`, and `0` lies in its image. Every `v` passes, `v = 5 - x` being
out of `range X₂ = {0}` included.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `[1, Eq. 7]` fails without a range row

## References

* [1] [S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC),
      2019.](../../../../../../references/2019/sadraddini-cdc-polytope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_inter_eq_counterexample : -- --- CONCL ---
    ∃ (x₁ x₂ : Vec ℝ 1) (X₁ X₂ X₂d : Mat ℝ 1 1) (H : Mat ℝ 2 1) (h : Vec ℝ 2),
      X₂ * X₂d * X₂ = X₂ ∧ X₂d * X₂ * X₂d = X₂d ∧ (X₂ * X₂d)ᵀ = X₂ * X₂d ∧
      (X₂d * X₂)ᵀ = X₂d * X₂ ∧
      HPolytope.ahPolytope x₁ X₁ (HPolytope.ineqs H h) ∩ HPolytope.ahPolytope x₂ X₂
          (HPolytope.ineqs H h)
        ≠ {x | ∃ (p₁ w : Vec ℝ 1), H *ᵥ p₁ ≤ h ∧
            H *ᵥ (X₂d *ᵥ (X₁ *ᵥ p₁) + (1 - X₂d * X₂) *ᵥ w) ≤ h + H *ᵥ (X₂d *ᵥ (x₂ - x₁)) ∧
            x = x₁ + X₁ *ᵥ p₁} := by -- --- PROOF ---
  refine ⟨0, ![5], 1, 0, 0, !![1; -1], ![1, 1], by simp, by simp, by simp, by simp, ?_⟩
  intro heq
  -- `0` passes the printed rows
  have hmem : (0 : Vec ℝ 1) ∈ {x : Vec ℝ 1 | ∃ (p₁ w : Vec ℝ 1),
      (!![1; -1] : Mat ℝ 2 1) *ᵥ p₁ ≤ ![1, 1] ∧
      (!![1; -1] : Mat ℝ 2 1) *ᵥ ((0 : Mat ℝ 1 1) *ᵥ ((1 : Mat ℝ 1 1) *ᵥ p₁)
        + (1 - (0 : Mat ℝ 1 1) * 0) *ᵥ w)
        ≤ ![1, 1] + (!![1; -1] : Mat ℝ 2 1) *ᵥ ((0 : Mat ℝ 1 1) *ᵥ (![5] - 0)) ∧
      x = 0 + (1 : Mat ℝ 1 1) *ᵥ p₁} :=
    ⟨0, 0, fun i => by fin_cases i <;> norm_num, fun i => by fin_cases i <;> norm_num, by simp⟩
  rw [← heq] at hmem
  -- but the second set is `{5}`
  obtain ⟨-, p₂, -, hp⟩ := hmem
  have := congrFun hp 0
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
