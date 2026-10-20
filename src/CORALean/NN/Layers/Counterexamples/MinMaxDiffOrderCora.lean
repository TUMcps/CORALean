module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `Layer.minMaxDiffOrderCora`: the error bound of a monotone activation as CORA computes it

`nnHelper.minMaxDiffOrder.m` (l. 48-60), branch for a layer of `monotonicity` at least 2 and a
linear polynomial `[a, b]`: with `ddiff = df - a` it calls `fzero(ddiff, [l u])` when `ddiff(l) *
ddiff(u) > 0`, and otherwise keeps `xs = [l,u]`. But `fzero` needs a sign change, `< 0`, and the
slope of a chord of a convex `f` lies between `df(l)` and `df(u)`, so the interior extremum of `f -
p` is missed. Read from the source, not run.

For `exp` on `[-1, 1]` with chord slope `m = (e - 1/e)/2` the code evaluates `f - p` at the end
points (`1.543`), while the minimum is `0.986`: the value `1` at `0` is below the lower bound.

## Inputs
* `root` – result of the root finder

## Hypotheses
* none

## Conclusion
* some point's difference to the line lies below CORA's lower bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `[diffl, diffu]` of `minMaxDiffOrder` for `f`, `df`, `coeffs = [a, b]`, the box
`[l, u]` and the root `root` that `fzero` would return. -/
noncomputable def Layer.minMaxDiffOrderCora (f df : ℝ → ℝ) (a b l u root : ℝ) : Interval ℝ :=
  let eps : ℝ := (2⁻¹ : ℝ) ^ 52
  -- ys = layer.f(xs) - polyval(coeffs,xs)
  let y : ℝ → ℝ := fun x => f x - (a * x + b)
  -- ddiff(l) * ddiff(u) > 0
  if (df l - a) * (df u - a) > 0 then
    -- xs = [l, u, fzero(ddiff, [l u])]
    ⟨min (min (y l) (y u)) (y root) - eps, max (max (y l) (y u)) (y root) + eps⟩
  else
    -- xs = [l, u]
    ⟨min (y l) (y u) - eps, max (y l) (y u) + eps⟩

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `f = df = exp` on `[-1, 1]` with the chord slope `m`, the point `0` has `f 0 - p 0`
below CORA's lower bound `diffl`, whatever `fzero` returns. -/
theorem Layer.minMaxDiffOrder_cora_counterexample (root : ℝ) : -- --- CONCL ---
    ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      Real.exp x - ((Real.exp 1 - Real.exp (-1)) / 2 * x + 0) <
        (Layer.minMaxDiffOrderCora Real.exp Real.exp ((Real.exp 1 - Real.exp (-1)) / 2) 0
          (-1) 1 root).inf := by -- --- PROOF ---
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hpos : 0 < Real.exp (-1) := Real.exp_pos _
  have hprod : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  have h3 : (1 : ℝ) / 3 < Real.exp (-1) := by nlinarith
  refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
  -- ddiff(l) < 0 < ddiff(u): no `fzero`
  have hneg : ¬ (Real.exp (-1) - (Real.exp 1 - Real.exp (-1)) / 2) *
      (Real.exp 1 - (Real.exp 1 - Real.exp (-1)) / 2) > 0 := by
    have h4 : Real.exp (-1) ≤ 1 / 2 := by nlinarith
    have hl : Real.exp (-1) - (Real.exp 1 - Real.exp (-1)) / 2 < 0 := by linarith
    have hu : 0 < Real.exp 1 - (Real.exp 1 - Real.exp (-1)) / 2 := by linarith
    exact not_lt.2 (mul_neg_of_neg_of_pos hl hu).le
  simp only [Layer.minMaxDiffOrderCora, hneg, if_false]
  have hmin : min (Real.exp (-1) - ((Real.exp 1 - Real.exp (-1)) / 2 * (-1) + 0))
      (Real.exp 1 - ((Real.exp 1 - Real.exp (-1)) / 2 * 1 + 0)) =
      (Real.exp 1 + Real.exp (-1)) / 2 := by
    rw [show Real.exp (-1) - ((Real.exp 1 - Real.exp (-1)) / 2 * (-1) + 0) =
        (Real.exp 1 + Real.exp (-1)) / 2 by ring,
      show Real.exp 1 - ((Real.exp 1 - Real.exp (-1)) / 2 * 1 + 0) =
        (Real.exp 1 + Real.exp (-1)) / 2 by ring, min_self]
  rw [hmin]
  have heps : ((2⁻¹ : ℝ) ^ 52) < 1 / 6 := by norm_num
  simp only [Real.exp_zero, mul_zero, add_zero, sub_zero]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
