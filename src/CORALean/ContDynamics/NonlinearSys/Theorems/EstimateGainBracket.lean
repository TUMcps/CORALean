module

public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGain
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# What `estimateGain`'s bisection buys

The soundness of line 16 of [1, Alg. 2] as written here: the gain reported sits between a
`φ⁽¹⁾` whose eq. (56) left-hand side is still under the right-hand side and one already over it,
and those two are `2^{-fuel}` apart. It is not a root: eq. (56)'s left-hand side is not shown
continuous here, so nothing says a crossing point exists. Line 13 of [2, Alg. 2] solves the same
equation, its (29) being (56) here. The two hypotheses are the starting bracket, `φ⁽¹⁾ = 0` under
the target and `φ⁽¹⁾ = 1` over it; where there is no crossing the theorem does not apply.

## Inputs
* `le` – comparison of reals
* `ζδ` – tuning constant
* `lam` – step scaling
* `rabs1` – abstraction radius at the horizon
* `rabsOpt` – abstraction radius at the optimal step
* `scalings` – number of scalings
* `fuel` – number of halvings

## Hypotheses
* `hlo` – zero gain passes
* `hhi` – unit gain fails

## Conclusion
* the gain is bracketed by a passing and a failing value

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
* [2] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control,
      2021.](../../../../../references/2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Each halving keeps a passing end and a failing end and halves what lies
between them. -/
private theorem aux_estimateGainSearch_bracket (le : ℝ → ℝ → Bool) (g : ℝ → ℝ)
    (target : ℝ) : -- --- CONCL ---
    ∀ (fuel : ℕ) (lo hi : ℝ), lo ≤ hi → le (g lo) target = true → le (g hi) target = false →
      ∃ a b : ℝ, le (g a) target = true ∧ le (g b) target = false ∧
        a ≤ step_estimateGainSearch le g target lo hi fuel ∧
        step_estimateGainSearch le g target lo hi fuel ≤ b ∧
        b - a = (hi - lo) / 2 ^ fuel := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hlehi hlo hhi
    rw [show step_estimateGainSearch le g target lo hi 0 = (lo + hi) / 2 from rfl]
    exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by norm_num⟩
  | succ k ih =>
    intro lo hi hlehi hlo hhi
    rw [show step_estimateGainSearch le g target lo hi (k + 1)
      = if le (g ((lo + hi) / 2)) target then
          step_estimateGainSearch le g target ((lo + hi) / 2) hi k
        else step_estimateGainSearch le g target lo ((lo + hi) / 2) k from rfl]
    split
    -- the midpoint still passes, so it becomes the new passing end
    · rename_i hc
      obtain ⟨a, b, ha, hb, h1, h2, h3⟩ := ih ((lo + hi) / 2) hi (by linarith) hc hhi
      exact ⟨a, b, ha, hb, h1, h2, by rw [h3, pow_succ]; ring⟩
    · rename_i hc
      obtain ⟨a, b, ha, hb, h1, h2, h3⟩ :=
        ih lo ((lo + hi) / 2) (by linarith) hlo (by simpa using hc)
      exact ⟨a, b, ha, hb, h1, h2, by rw [h3, pow_succ]; ring⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] line 16: the gain reported is bracketed to within `2^{-fuel}`
between a passing and a failing value of eq. (56). -/
theorem estimateGain_bracket {le : ℝ → ℝ → Bool} (ζδ lam rabs1 rabsOpt : ℝ)
    (scalings fuel : ℕ)
    (hlo : le (∏ j ∈ Finset.range scalings, interpGain ζδ 0 j)
      (lam * rabsOpt / rabs1) = true)
    (hhi : le (∏ j ∈ Finset.range scalings, interpGain ζδ 1 j)
      (lam * rabsOpt / rabs1) = false) : -- --- CONCL ---
    ∃ a b : ℝ,
      le (∏ j ∈ Finset.range scalings, interpGain ζδ a j) (lam * rabsOpt / rabs1) = true ∧
      le (∏ j ∈ Finset.range scalings, interpGain ζδ b j) (lam * rabsOpt / rabs1) = false ∧
      a ≤ estimateGain le ζδ lam rabs1 rabsOpt scalings fuel ∧
      estimateGain le ζδ lam rabs1 rabsOpt scalings fuel ≤ b ∧
      b - a = 1 / 2 ^ fuel := by -- --- PROOF ---
  obtain ⟨a, b, ha, hb, h1, h2, h3⟩ := aux_estimateGainSearch_bracket le
    (fun φ1 => ∏ j ∈ Finset.range scalings, interpGain ζδ φ1 j) (lam * rabsOpt / rabs1)
    fuel 0 1 (by norm_num) hlo hhi
  exact ⟨a, b, ha, hb, h1, h2, by rw [h3]; norm_num⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
