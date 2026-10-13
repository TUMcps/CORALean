module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `ConZonotope.supportFuncUpperCora`: the `'upper'` support function as CORA's code computes it

`@conZonotope/supportFunc_.m`, `type = 'upper'`:

```
if isempty(cZ.A) || all(all(cZ.A == 0))                           % (l. 49)
    [val,x,ksi] = aux_supportFunc_unconstrained(cZ,dir,type);
    return
end
...                                                                % the linear program
```

CORA's `cZ.A`, `cZ.b` are the equality rows `A ξ = b` (here `P.Ae`, `P.be`). An all-zero `A`
is read as "no constraints", whatever `b` is, though `0 ξ = b` with `b ≠ 0` has no solution.
The unconstrained branch returns `supremum(interval(dir'*cZ))`, the support value of the
zonotope `c + G [-1,1]^h`, `dir·c + Σ |dir·Gⱼ|`. The linear program of the constrained branch is
the parameter `lp`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CORA's `val` for `supportFunc_(cZ, dir, 'upper')`; `lp` is the value of the linear program
of the constrained branch. -/
noncomputable def ConZonotope.supportFuncUpperCora (cZ : ConZonotope (Vec ℝ n))
    (dir : Vec ℝ n →ₗ[ℝ] ℝ) (lp : EReal) : EReal :=
  -- isempty(cZ.A) || all(all(cZ.A == 0))
  if ∀ i ξ, cZ.P.Ae i ξ = 0 then
    -- aux_supportFunc_unconstrained: val = supremum(interval(dir'*cZ))
    (((dir cZ.c + ∑ j, |dir (cZ.G j)| : ℝ)) : EReal)
  else lp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
