module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# `Alg. 2`'s loop state

`MinBackReachState`: what one iteration of [1, Alg. 2] hands the next.

## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 2] hands the next, over the time type `T`, the zonotope type
`Z` and the constrained-zonotope type `C` of whichever layer runs it: the real one at `ℝ` and
`Real.Zonotope`, the float one at `𝕋` and `Float.Zonotope`. -/
structure LinearSys.MinBackReachStateOf (T Z C : Type) where
  /-- `t_k`, line 8. -/
  t : T
  /-- `Ẑ_{W₀}(-t_k)`, line 9. -/
  ZW₀ : Z
  /-- `Ẑ_{U₀}(-t_k)`, line 12. -/
  ZU₀ : Z
  /-- `R̂^∃(-τ_{k-1})`, line 11. -/
  R : C

/-- The state over the reals. -/
abbrev LinearSys.MinBackReachState (n : ℕ) : Type :=
  LinearSys.MinBackReachStateOf ℝ (Zonotope (Vec ℝ n)) (ConZonotope (Vec ℝ n))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
