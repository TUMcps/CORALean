module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Interval.supportFuncUpperCora`: `supportFunc(I, dir, 'upper')` as CORA's code computes it

`@interval/supportFunc_.m` (l. 49-53) picks the vertex and takes one inner product:

```
idx = sign(dir) == -1;
x = I.sup;  x(idx) = I.inf(idx);
val = dir'*x;
```

For an unbounded box `x` holds `±Inf`, and a zero entry of `dir` on such a coordinate gives
`0*Inf = NaN` in IEEE arithmetic, which the sum carries. Two dimensions, `none` for `NaN`, `±Inf`
as `EReal`; the `Inf - Inf` of a sum is not modelled, no entry of the example needs it. The
`'lower'` and `'range'` types do the same. Read from the source, not run.

# CORA's `supportFunc` of a half-bounded box with a zero direction entry is `NaN`

`supportFunc(interval([0; -Inf], [1; Inf]), [1; 0])` is `1*1 + 0*Inf = NaN` in CORA, while the
second coordinate does not enter the support function and the answer is `1`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA returns NaN although the attained maximum is one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- IEEE `a * b` on `EReal`: `0 * (±Inf)` is `NaN` (`none`). -/
noncomputable def Interval.ieeeMulCora (a b : EReal) : Option EReal :=
  if (a = 0 ∧ (b = ⊤ ∨ b = ⊥)) ∨ (b = 0 ∧ (a = ⊤ ∨ a = ⊥)) then none else some (a * b)

/-- CORA's `val` of `supportFunc(interval(lo, hi), dir, 'upper')` in two dimensions: the vertex
`x` (`sup`, or `inf` where `sign(dir) == -1`) and the sum of the entries `dir(i) * x(i)`, `NaN`
(`none`) as soon as one product is. -/
noncomputable def Interval.supportFuncUpperCora (dir : Fin 2 → ℝ)
    (lo hi : Fin 2 → EReal) : Option EReal :=
  -- x = I.sup; x(sign(dir) == -1) = I.inf
  let x : Fin 2 → EReal := fun i => if dir i < 0 then lo i else hi i
  -- val = dir'*x
  (Interval.ieeeMulCora (dir 0) (x 0)).bind fun a =>
    (Interval.ieeeMulCora (dir 1) (x 1)).map fun b => a + b


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `I = [0, 1] x (-Inf, Inf)` and `dir = (1, 0)` CORA's value is `NaN`, although `1` is the
largest of `dir . x` over the box and is attained. -/
theorem Interval.supportFuncUpper_cora_counterexample :
    Interval.supportFuncUpperCora ![1, 0] ![0, ⊥] ![1, ⊤] = none ∧
      (∃ x : Fin 2 → ℝ, 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 1 * x 0 + 0 * x 1 = 1) ∧
      ∀ x : Fin 2 → ℝ, 0 ≤ x 0 → x 0 ≤ 1 → 1 * x 0 + 0 * x 1 ≤ 1 := by
  refine ⟨?_, ⟨![1, 0], by simp⟩, fun x _ h => by linarith⟩
  simp [Interval.supportFuncUpperCora, Interval.ieeeMulCora]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
