module

public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionUnique

@[expose] public section

/-!
# A solution through a zero of a Lipschitz field stays there

If `F` vanishes at `y(a)`, the constant curve and `y` both solve `ẋ = F(x)` from `a`, so by
uniqueness `y` is constant from `a` on. This is what keeps the scaled solution of [1, Sec. 3.2]
from crossing the guard: `g(x) = (b - a·x) / ‖a‖` vanishes on it, and `g · f` with it.

## Inputs
* `F` – vector field
* `K` – Lipschitz constant
* `y` – curve
* `a` – start time
* `t` – end time

## Hypotheses
* `hF` – field is Lipschitz
* `hy` – curve solves the field
* `hFa` – field vanishes at the start point

## Conclusion
* the curve is constant on the interval

## References

* [1] [S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability
      Analysis of Hybrid Automata". Formal Modeling and Analysis of Timed Systems,
      2017.](../../../../../references/2017/bak-formats-time-triggered-conversion.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set
open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A solution of `ẋ = F(x)` on `[a, t]` through a zero of `F` at `a` is constant there. -/
theorem lipschitzSolution_const_of_zero {F : X → X} {K : ℝ≥0} (hF : LipschitzWith K F)
    {y : ℝ → X} {a t : ℝ} (hy : ∀ u ∈ Icc a t, HasDerivAt y (F (y u)) u)
    (hFa : F (y a) = 0) : -- --- CONCL ---
    ∀ u ∈ Icc a t, y u = y a := by -- --- PROOF ---
  intro u hu
  have := lipschitzSolution_unique hF (z := fun v => y (a + v)) (w := fun _ => y a) (M := t - a)
    (fun v hv => by
      have := (hy (a + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩).comp_const_add a v
      simpa using this)
    (fun v _ => by
      have := hasDerivAt_const v (y a)
      rwa [← hFa] at this) (by simp) (u - a) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
