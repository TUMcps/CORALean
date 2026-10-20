module

public import CORALean.ContSet.Interval.Real.Operations.Power
public import CORALean.ContSet.Interval.Real.Operations.Times
public import CORALean.ContSet.Interval.Real.Operations.Smul
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The natural extension depends on the expression

[1, Sec. 2 (natural extension)]: `f(x₁, x₂) = x₁² - 2x₁x₂ + x₂²` has the natural extension
`[x₁]² - 2[x₁][x₂] + [x₂]²`, which on `[x₁] = [x₂] = [0, 1]` evaluates to `[-2, 2]`; written
`(x₁ - x₂)²`, it evaluates to `([x₁] - [x₂])² = [0, 1]`, which is the range of `f` on the box
and lies in `[-2, 2]`. Evaluated with CORALean's interval operations — `power`, `times`,
`smul`, `minus`, `plus` — at one coordinate, the two variables entering as the same
interval, which interval arithmetic treats as independent: the dependency problem.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the natural extension gives the wider interval, the rewritten form the exact range

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.naturalExtension_dependency : -- --- CONCL ---
    let X : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩
    let natural := ((X.power 2).minus ((X.times X).smul 2)).plus (X.power 2)
    let rewritten := (X.minus X).power 2
    (natural.inf 0 = -2 ∧ natural.sup 0 = 2) ∧ (rewritten.inf 0 = 0 ∧ rewritten.sup 0 = 1) ∧
      Set.image2 (fun a b : ℝ => a ^ 2 - 2 * a * b + b ^ 2) (Set.Icc 0 1) (Set.Icc 0 1) =
        Set.Icc 0 1 := by -- --- PROOF ---
  intro X natural rewritten
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  rotate_left 4
  · -- the range: `(a - b)² ∈ [0, 1]` on the box, and `t = (√t - 0)²` takes every value
    ext t
    constructor
    · rintro ⟨a, ⟨ha0, ha1⟩, b, ⟨hb0, hb1⟩, rfl⟩
      show 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 ∧ a ^ 2 - 2 * a * b + b ^ 2 ≤ 1
      constructor <;> nlinarith [sq_nonneg (a - b), mul_nonneg ha0 hb0]
    · rintro ⟨ht0, ht1⟩
      refine ⟨Real.sqrt t, ⟨Real.sqrt_nonneg t, Real.sqrt_le_one.mpr ht1⟩, 0,
        ⟨le_rfl, zero_le_one⟩, ?_⟩
      simp [Real.sq_sqrt ht0]
  -- the four bounds, by evaluating the operations' corner formulas
  all_goals (simp [natural, rewritten, X, Interval.power, Interval.minus, Interval.times,
      Interval.smul, Interval.plus, Interval.mulLo, Interval.mulHi, Entrywise.ofEntry,
      Entrywise.entry]; try norm_num)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
