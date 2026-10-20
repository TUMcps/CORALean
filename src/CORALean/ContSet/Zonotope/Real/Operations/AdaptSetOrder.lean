module

public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrderLoop

@[expose] public section

/-!
# `Alg. 3`: the set representation size for one step

[1, Alg. 3] shrinks `Φ_set` while the reduction it costs stays inside eq.
(13)'s share of what is left of the `ε_S` budget: read `param(PR)`, then
`decr` and `red` until the next decrement would overshoot the share or there
is nothing left to decrement. `Φ_set` is the *order* here, `reduceBox` being
indexed by `ρ = γ/n` [1, Def. 2], so one `decr` steps `n` generators.

One departure, deliberate. The loop keeps the last order that *passed*; [1]'s
line 7 as printed returns the first that failed.

## Inputs
* `le` – decidable comparison on reals
* `Z` – zonotope
* `εSmax` – total set-error budget
* `εSacc` – error already accumulated
* `tf` – final time
* `ti` – current time
* `Δt` – time step

## Output
* reduction order and the error it accumulates

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the order to reduce `PR([0,t_{i+1}])` to, and the `ε_S` that
reduction accumulates. -/
noncomputable def Zonotope.adaptSetOrder (le : ℝ → ℝ → Bool) (Z : Zonotope (Vec ℝ n))
    (εSmax εSacc tf ti Δt : ℝ) : ℕ × ℝ :=
  -- 1. the admissible share of the remaining budget, `ε_{S,i}`, eq. (13)
  let εSi := (εSmax - εSacc) / (tf - ti) * Δt
  -- 2. `Φ_set ← param(PR)`, reducing nothing
  let Φset := Z.h
  -- 3. lines 3-7: `decr` and `red` while the reduction is admissible
  let Φset' := Zonotope.adaptSetOrderLoop le Z εSi Φset Φset
  -- 8. accumulate the reduction's error, eq. (12)
  (Φset', εSacc + Z.reduceBoxError Φset')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
