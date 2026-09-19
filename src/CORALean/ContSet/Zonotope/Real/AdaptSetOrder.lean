import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox
import CORALean.Global.EuclideanNorm

/-!
# `Alg. 3`: the set representation size for one step

[1, Alg. 3] shrinks `Φ_set` while the reduction it costs stays inside eq.
(13)'s share of what is left of the `ε_S` budget: read `param(PR)`, then
`decr` and `red` until the next decrement would overshoot the share or there
is nothing left to decrement. `Φ_set` is the *order* here, `reduceBox` being
indexed by `ρ = γ/n` [1, Def. 2], so one `decr` steps `n` generators.

`ε_S([t_i,t_{i+1}])` is `reduceBoxError`: `err(·)` — the Euclidean radius of
the box over-approximation, [1, Prop. 1] — at the very box `reduceBox`
absorbs the dropped generators into.

Two departures, both deliberate. The loop keeps the last order that *passed*;
[1]'s line 7 as printed returns the first that failed. And it needs no
invented fuel: `Z.h` decrements reach every order there is, so the bound is
the set's own size — unlike `Alg. 2`, whose step sweep has none.

Neither `Nat.find` nor `Classical.choose`, unlike `reduceBoxOrder` beside it.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- `[1]`'s `ε_S([t_i,t_{i+1}])`: `err(·)` at the box a reduction to order `o`
absorbs the generators it drops into. -/
noncomputable def Zonotope.reduceBoxError (Z : Zonotope (Vec ℝ n)) (o : ℕ) : ℝ :=
  ‖fun j => (Z.reduceBox o).absBound j‖₂

/-- Lines 3-7: decrement the order while the reduction one step down still
clears the share, and keep the last order that did. -/
noncomputable def Zonotope.adaptSetOrderLoop (le : ℝ → ℝ → Bool)
    (Z : Zonotope (Vec ℝ n)) (εSi : ℝ) : ℕ → ℕ → ℕ
  | Φset, 0 => Φset
  | 0, _ + 1 => 0
  | Φset + 1, k + 1 =>
    if le (Z.reduceBoxError Φset) εSi then Zonotope.adaptSetOrderLoop le Z εSi Φset k else Φset + 1


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the order to reduce `PR([0,t_{i+1}])` to, and the `ε_S` that
reduction accumulates. -/
noncomputable def Zonotope.adaptSetOrder (le : ℝ → ℝ → Bool) (Z : Zonotope (Vec ℝ n))
    (εSmax εSacc tf ti Δt : ℝ) : ℕ × ℝ :=
  let εSi := (εSmax - εSacc) / (tf - ti) * Δt              -- 1. the admissible share, eq. (13)
  let Φset := Z.h                                          -- 2. param(PR), reducing nothing
  let Φset' := Zonotope.adaptSetOrderLoop le Z εSi Φset Φset  -- 3.-7. decrement while admissible
  (Φset', εSacc + Z.reduceBoxError Φset')                  -- 8. accumulate, eq. (12)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
