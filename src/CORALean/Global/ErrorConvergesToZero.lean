import CORALean.Global.Mathlib

/-!
# `Assumption 1`: a step error converges to zero

[1, Assumption 1]: floating-point errors neglected, `ε_H([t_i,t_{i+1}]) → 0` and
`ε_P([t_i,t_{i+1}]) → 0` as `Δt_i → 0`. Stated once, as a predicate over one
step-error function of the step length alone — the interval's start plays no
role, on a par with `SuperlinearDecrease` — so `Assumption 1` itself is this
predicate holding of both `ε_H` and `ε_P`, and `Prop. 3`/`Prop. 4` are what
discharge it for [1]'s own `ε_H` (eq. 21) and `ε_P` (eq. 22).

Not an `axiom`: a named property unfolding to a plain `Filter.Tendsto`, so a
step-error function either has it, proved, or the row says why not.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Assumption 1]: `ε` converges to `0` as the step length shrinks to `0`. -/
def ErrorConvergesToZero (ε : ℝ → ℝ) : Prop :=
  Tendsto ε (𝓝[>] (0:ℝ)) (𝓝 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
