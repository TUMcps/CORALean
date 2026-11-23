module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A relation of a neuron's values is a row on the factors

A neuron's input `x = c_i + g_iᵀ β + δ_i` and output `y = c_o + g_oᵀ β + δ_o`, the rests bounded by
`|δ_i| ≤ r_i`, `|δ_o| ≤ r_o`, satisfying `a x + b y ≤ e` give the row
`(a g_i + b g_o)ᵀ β ≤ e - a c_i - b c_o + |a| r_i + |b| r_o` on the factors. The rows of the dual
certificate are of this kind (`ConZonotope.dualBound`): a split `-x ≤ 0` or `x ≤ 0` (`b = 0`), and
the ReLU faces `-y ≤ 0`, `x - y ≤ 0` and `y - s x ≤ -s l` of the chord `s = u / (u - l)`.

## Inputs
* `a` – the relation's coefficient of the input
* `b` – the relation's coefficient of the output
* `e` – the relation's bound
* `ci` – the input's center
* `co` – the output's center
* `ri` – the input's rest radius
* `ro` – the output's rest radius
* `x` – the neuron's input value
* `y` – the neuron's output value
* `δi` – the input's rest
* `δo` – the output's rest
* `gi` – the input's generator row
* `go` – the output's generator row
* `β` – factors

## Hypotheses
* `hx` – the input in terms of the factors and its rest
* `hy` – the output in terms of the factors and its rest
* `hδi` – the input's rest within its radius
* `hδo` – the output's rest within its radius
* `h` – the relation holds

## Conclusion
* the row holds on the factors
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.phaseRow_holds {a b e ci co ri ro x y δi δo : ℝ} {gi go β : Vec ℝ q}
    (hx : x = ci + ∑ j, gi j * β j + δi) (hy : y = co + ∑ j, go j * β j + δo)
    (hδi : |δi| ≤ ri) (hδo : |δo| ≤ ro) (h : a * x + b * y ≤ e) : -- --- CONCL ---
    ∑ j, (a * gi j + b * go j) * β j
      ≤ e - a * ci - b * co + |a| * ri + |b| * ro := by -- --- PROOF ---
  have hsum : ∑ j, (a * gi j + b * go j) * β j
      = a * ∑ j, gi j * β j + b * ∑ j, go j * β j := by
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the rests at their worst
  have hai : -(a * δi) ≤ |a| * ri := by
    have := abs_mul a δi
    linarith [neg_abs_le (a * δi), mul_le_mul_of_nonneg_left hδi (abs_nonneg a)]
  have hbo : -(b * δo) ≤ |b| * ro := by
    have := abs_mul b δo
    linarith [neg_abs_le (b * δo), mul_le_mul_of_nonneg_left hδo (abs_nonneg b)]
  subst hx hy
  rw [hsum]
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
