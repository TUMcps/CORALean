module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-!
# `Taylm.asinRemainderUpperCora`: the remainder of CORA's `asin(taylm)`

`@taylm/asin.m`, `aux_s_asin` (l. 89-91):

```
res.remainder = res.remainder + 1/factor * remPow .* asin(interval(0,1).*rem).^(obj.max_order+1);
```

with `factor = (k+1)!` and `remPow = interval(T^(k+1))`. The Lagrange remainder of `asin` needs its
`(k+1)`-th derivative at an intermediate point; the code uses `asin(θ·rem)^(k+1)`, a power of the
function. For `k + 1` even and `rem = [-r, r]` the interval power is `[0, (asin r)^(k+1)]` and
`remPow = [0, r^(k+1)]`: the upper end is the definition below. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The upper end of CORA's remainder interval for the variable on `[-r, r]`, order `k`, `k + 1`
even: `r^(k+1) * (asin r)^(k+1) / (k+1)!`. -/
noncomputable def Taylm.asinRemainderUpperCora (k : ℕ) (r : ℝ) : ℝ :=
  r ^ (k + 1) * Real.arcsin r ^ (k + 1) / ((k + 1).factorial : ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
