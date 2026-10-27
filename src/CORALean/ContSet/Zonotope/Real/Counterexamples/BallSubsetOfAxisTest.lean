module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# `[1, Lemma 5]` with the test as printed

The test checks `ν eᵢ ∈ Z`, and its complexity paragraph checks the feasibility of
`ν eᵢ = G x + z̄`: the point `ν eᵢ` itself, not `z̄ + ν eᵢ`. For `Z = [5, 7] = 6 + [-1, 1] ⊂ ℝ¹`
and `ν = 6` the test passes, `6 ∈ Z`, but `ν²/n = 36` is no lower bound on `⌊Z⌋² = 1`: the ball of
radius `6` around `6` reaches `12 ∉ Z`. Measured from the center the lemma holds
(`ball_subset_of_axis_test`); [1, Thm. 3] applies it to a transformed zonotope whose center is
generally not the origin.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* axis points lie in `Z` but the ball around its center does not

## References

* [1] [V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". 2020 American Control Conference (ACC),
      2020.](../../../../../../references/2020/gassmann-acc-zonotope-ellipsoid.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ball_subset_of_axis_test_counterexample : -- --- CONCL ---
    ∃ (Z : Zonotope (Vec ℝ 1)) (ν : ℝ), 0 ≤ ν ∧
      (∀ i : Fin 1, ν • (Pi.single i 1 : Vec ℝ 1) ∈ Z.construct) ∧
      ¬ ∀ x : Vec ℝ 1, ‖x‖₂ ≤ √(ν ^ 2 / 1) → Z.c + x ∈ Z.construct := by -- --- PROOF ---
  refine ⟨⟨1, ![6], fun _ => ![1]⟩, 6, by norm_num, fun i => ⟨fun _ => 0, fun _ => by simp, ?_⟩,
    fun h => ?_⟩
  -- `6 = 6 + 0`
  · funext a
    fin_cases a
    fin_cases i
    simp
  -- `6 + 6 = 12` is not `6 + β` with `|β| ≤ 1`
  · obtain ⟨β, hβ, heq⟩ := h ![6] (by simp [norm₂])
    have := congrFun heq 0
    simp at this
    have hb := abs_le.mp (hβ 0)
    linarith [hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
