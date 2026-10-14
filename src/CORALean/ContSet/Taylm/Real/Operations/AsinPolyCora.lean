module

public import CORALean.ContSet.Taylm.Real.Operations.AsinFactor1Cora
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-!
# `Taylm.asinPolyCora`: the polynomial of CORA's `asin(taylm)`

`@taylm/asin.m`, `aux_s_asin`, for the variable (centre `c_f = 0`, so `T = obj`):

```
for i = 1:obj.max_order
    factor = factor * i;  T_factor = T_factor .* T;
    if mod(i,2) == 1
        factor1 = factor1 .* aux_dasin(i);
        T1 = T1 + T_factor .* factor1 ./ factor;
    end
end
```

with `aux_dasin(k) = (k-2)^2` for `k ≥ 3` and `1` below, from `T1 = asin(0) = 0`. Read from the
source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polynomial of the model of `asin x` at the variable `x`, order `k`: the odd terms
`x^i * factor1 / i!` of the loop. -/
noncomputable def Taylm.asinPolyCora (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    if i % 2 = 1 then x ^ i * Taylm.asinFactor1Cora i / (i.factorial : ℝ) else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
