module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# CORA's scaling branch of `interval/contains_` for a point, as printed

`@interval/contains_.m` l. 68-73: for numeric `S` with `scalingToggle`,
`c = center(I); scaling = abs(S)./(abs([I.inf-c I.sup-c])); res = scaling <= 1 + tol`.
Taken as printed, in one dimension: `abs(S)` where `abs(S - c)` is meant, so `res` tests
`S ∈ [-r, r]` for the radius `r`, not `S ∈ I`. The result is a `1 × 2` row (one entry per
column of `[I.inf-c I.sup-c]`), here `Fin 2 → Prop`. `scalingToggle` is set by
`contSet/contains.m` l. 87-91 when `nargout >= 3`, i.e. `[res,cert,scaling] = contains(I,p)`.
Not modelled: the `n × 2` shapes in higher dimension, `NaN` or `Inf` for a degenerate `I`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `res` in the scaling branch: `abs(S)` over `abs(I.inf - c)`, `abs(I.sup - c)`. -/
noncomputable def Interval.containsScalingCora (I : Interval (Vec ℝ 1)) (S : Vec ℝ 1)
    (tol : ℝ) : Fin 2 → Prop :=
  let c := (I.inf 0 + I.sup 0) / 2
  let bounds : Fin 2 → ℝ := fun j => |if j = 0 then I.inf 0 - c else I.sup 0 - c|
  let scaling : Fin 2 → ℝ := fun j => |S 0| / bounds j
  fun j => scaling j ≤ 1 + tol

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
