module

public import CORALean.Global.FeasibleSolutionSet
public import CORALean.Global.PredictedSolutionSet

@[expose] public section

/-!
# The feasible solution set is the predicted set met with the last strip

[1, Sec. 3]: the set of [1, Def. 1] after `N + 1` measurements, which has met every measurement and
every bound on the parameter's rate of change, is the recursion's `FSS_{N+1}` (here
`predictedSolutionSet … N`, the parameters before the last measurement) met with the strip of the
last measurement `F_{d(N+1)}`. This is what lets the recursion `FSS_{k+1} = (FSS_k ∩ F_dk) ⊕ γ Bⁿ`
stand for [1, Def. 1]'s set, which the paper does not prove. Induction on `N`; a run for `N + 2`
steps is a run for `N + 1` and one more step.

## Inputs
* `Θ₀` – initial parameter set
* `r` – regressor vectors
* `y` – measurements
* `σ` – error bound
* `γ` – expansion per step
* `N` – number of earlier measurements

## Hypotheses
* none

## Conclusion
* the feasible set is the predicted set met with the last measurement's strip

## References

* [1] [J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control,
      2006.](../../../references/2006/bravo-tac-bounded-error-identification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_feasible_succ (Θ₀ : Set (Vec ℝ n)) (r : ℕ → Vec ℝ n) (y : ℕ → ℝ) (σ : ℝ)
    (γ : Vec ℝ n) (N : ℕ) : -- --- CONCL ---
    feasibleSolutionSet Θ₀ r y σ γ (N + 2) =
      (feasibleSolutionSet Θ₀ r y σ γ (N + 1) + {b | ∀ i, |b i| ≤ γ i}) ∩
        {θ | |r (N + 2) ⬝ᵥ θ - y (N + 2)| ≤ σ} := by -- --- PROOF ---
  ext θ
  constructor
  · -- the run up to `N + 1` is a run for the smaller set, and the last step is the box
    rintro ⟨θs, rfl, h1, hy, hs⟩
    refine ⟨⟨θs (N + 1), ⟨θs, rfl, h1, fun k hk hkN => hy k hk (by omega),
      fun k hk hkN => hs k hk (by omega)⟩, θs (N + 2) - θs (N + 1), fun i => ?_, by simp⟩, ?_⟩
    · simpa using hs (N + 2) (by omega) le_rfl i
    · show |r (N + 2) ⬝ᵥ θs (N + 2) - y (N + 2)| ≤ σ
      rw [abs_sub_comm]; exact hy (N + 2) (by omega) le_rfl
  · -- extend the run of `a` by `θ = a + b` at the step `N + 2`
    rintro ⟨⟨_, ⟨θs, rfl, h1, hy, hs⟩, b, hb, rfl⟩, hF⟩
    refine ⟨fun k => if k = N + 2 then θs (N + 1) + b else θs k, by simp, by simpa using h1,
      fun k hk hkN => ?_, fun k hk hkN i => ?_⟩
    · -- the old measurements, and the new one at `N + 2`
      by_cases hk' : k = N + 2
      · subst hk'
        beta_reduce
        rw [if_pos rfl, abs_sub_comm]
        exact hF
      · simpa [hk'] using hy k hk (by omega)
    · by_cases hk' : k = N + 2
      · -- the new step is the box
        subst hk'; simpa using hb i
      · -- an old step
        have h2 : k - 1 ≠ N + 2 := by omega
        simpa [hk', h2] using hs k hk (by omega) i


-- =======================================  MAIN THEOREM  ======================================= --

theorem feasibleSolutionSet_eq_predicted (Θ₀ : Set (Vec ℝ n)) (r : ℕ → Vec ℝ n) (y : ℕ → ℝ)
    (σ : ℝ) (γ : Vec ℝ n) (N : ℕ) : -- --- CONCL ---
    feasibleSolutionSet Θ₀ r y σ γ (N + 1) = predictedSolutionSet Θ₀ r y σ γ N ∩
      {θ | |r (N + 1) ⬝ᵥ θ - y (N + 1)| ≤ σ} := by -- --- PROOF ---
  induction N with
  | zero =>
    -- one measurement: the run is the point itself
    ext θ
    constructor
    · rintro ⟨θs, rfl, h1, hy, -⟩
      refine ⟨h1, ?_⟩
      show |r 1 ⬝ᵥ θs 1 - y 1| ≤ σ
      rw [abs_sub_comm]; exact hy 1 le_rfl le_rfl
    · rintro ⟨h1, hF⟩
      exact ⟨fun _ => θ, rfl, h1, fun k hk hkN => by
        obtain rfl : k = 1 := by omega
        show |y 1 - r 1 ⬝ᵥ θ| ≤ σ
        rw [abs_sub_comm]; exact hF, fun k hk hkN => by omega⟩
  | succ N ih =>
    -- one more step: the box, then the strip
    rw [aux_feasible_succ, ih]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
