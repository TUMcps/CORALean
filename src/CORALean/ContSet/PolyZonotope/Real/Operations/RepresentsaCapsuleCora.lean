module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.Global.Tensor

@[expose] public section

/-!
# `PolyZonotope.representsaCapsuleCora`: the `'capsule'` test as CORA's code runs

`@polyZonotope/representsa_.m` reads, for `type = 'capsule'` (l. 65-67),

```
% 1D, a point, or maximum one generator
res = n == 1 || isPoint && size(pZ.G,2) + size(pZ.GI) <= 1;
```

`size(pZ.GI)` is the row `[n, size(pZ.GI,2)]`, not a number (`size(pZ.GI,2)` was meant), so the
right operand of `&&` is a `1 × 2` logical array. MATLAB's `&&` accepts only operands
convertible to a logical scalar, and raises `Operands to the || and && operators must be
convertible to logical scalar values` once the left operand `isPoint` is true. The branch is
reached for `n ≥ 2` (else `n == 1` short-circuits) and a point (`isPoint`: no generators after
`compact_`); for any other set `isPoint` is false and the `&&` short-circuits. Read from the
source, not run.

`isPoint` is modelled as no stored generator, which is already compact.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `res` for `representsa_(pZ, 'capsule')` (one output); `none` is the MATLAB error. -/
def PolyZonotope.representsaCapsuleCora (pZ : PolyZonotope (Vec ℝ n)) : Option Bool :=
  -- isPoint = isempty(pZ.G) && isempty(pZ.GI)
  let isPoint := pZ.h == 0 && pZ.q == 0
  -- size(pZ.G,2) + size(pZ.GI) <= 1, with size(pZ.GI) = [n, size(pZ.GI,2)]
  let rhs : List Bool := [decide (pZ.h + n ≤ 1), decide (pZ.h + pZ.q ≤ 1)]
  -- n == 1 || ...
  if n == 1 then some true
  -- isPoint && rhs: false short-circuits
  else if !isPoint then some false
  -- a non-scalar operand of `&&`
  else match rhs with
    | [b] => some b
    | _ => none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
