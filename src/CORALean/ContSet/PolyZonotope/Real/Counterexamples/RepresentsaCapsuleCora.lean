module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.Global.Tensor
public import CORALean.ContSet.Capsule.Real.Theorems.OfPointMemIff

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
convertible to a logical scalar and raises an error once `isPoint` is true. The branch is
reached for `n ≥ 2` and a point (`isPoint`: no generators after `compact_`), modelled as no
stored generator, which is already compact. Read from the source, not run.

# CORA's `polyZonotope/representsa_(pZ, 'capsule')` errors on a point in dimension two or more

A polynomial zonotope without generators, `{c}` with `c ∈ ℝ²`, reaches the `&&` of l. 67 with a
true left operand and the `1 × 2` array on the right, which MATLAB rejects. A point is a
capsule, so the answer is `true`.

## Inputs
* `c` – point

## Hypotheses
* none

## Conclusion
* CORA's capsule test crashes on a point
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
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

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The polynomial zonotope `{c}`: no factor, no generator. -/
def PolyZonotope.aux_point (c : Vec ℝ 2) : PolyZonotope (Vec ℝ 2) :=
  ⟨0, 0, 0, c, Fin.elim0, fun k => k.elim0, Fin.elim0⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's test errors on `{c}`, which is the capsule `Capsule.ofPoint c`. -/
theorem PolyZonotope.representsa_capsule_cora_crash (c : Vec ℝ 2) :
    (PolyZonotope.aux_point c).representsaCapsuleCora = none ∧
      (PolyZonotope.aux_point c).construct = (Capsule.ofPoint c).construct := by
  refine ⟨by simp [PolyZonotope.representsaCapsuleCora, PolyZonotope.aux_point], ?_⟩
  ext x
  rw [Capsule.mem_ofPoint_iff]
  simp [PolyZonotope.construct, PolyZonotope.aux_point, eq_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
