module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# `Taylm.asinDasinCora`: `aux_dasin` of CORA's `asin(taylm)`

`@taylm/asin.m`: `aux_dasin(k) = (k-2)^2` for `k >= 3`, `1` below.

# `Taylm.asinFactor1Cora`: the running `factor1` of CORA's `asin(taylm)`

`@taylm/asin.m` multiplies `factor1` by `aux_dasin(i)` at every odd step `i` of its loop.

# `Taylm.asinPolyCora`: the polynomial of CORA's `asin(taylm)`

`@taylm/asin.m`, `aux_s_asin`, for the variable (center `c_f = 0`, so `T = obj`):

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

# `Taylm.asinRemainderUpperCora`: the remainder of CORA's `asin(taylm)`

`@taylm/asin.m`, `aux_s_asin` (l. 89-91):

```
res.remainder = res.remainder + 1/factor * remPow .* asin(interval(0,1).*rem).^(obj.max_order+1);
```

with `factor = (k+1)!` and `remPow = interval(T^(k+1))`. The Lagrange remainder of `asin` needs its
`(k+1)`-th derivative at an intermediate point; the code uses `asin(θ·rem)^(k+1)`, a power of the
function. For `k + 1` even and `rem = [-r, r]` the interval power is `[0, (asin r)^(k+1)]` and
`remPow = [0, r^(k+1)]`: the upper end is the definition below. Read from the source, not run.

# CORA's `asin(taylm)` remainder is too small

For `taylm(interval(-1, 1), 7)` the polynomial is `x + x³/6 + 3x⁵/40 + 5x⁷/112` and the remainder
interval `[0, (π/2)⁸/8!] ≈ [0, 0.00092]` (the unit test `test_taylm_asin` asserts it). At
`x = 1` the model is therefore `[1.2863, 1.2872]`, while `asin 1 = π/2 ≈ 1.5708`: the true error
of the polynomial is `0.2845`. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's arcsine enclosure at one misses arcsin one from above
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `aux_dasin(k)`. -/
def Taylm.asinDasinCora (k : ℕ) : ℝ := if 3 ≤ k then ((k : ℝ) - 2) ^ 2 else 1


-- The model: CORA's code as printed, kept only to be refuted.
/-- The value of `factor1` after step `i`. -/
def Taylm.asinFactor1Cora : ℕ → ℝ
  | 0 => 1
  | i + 1 => if (i + 1) % 2 = 1 then Taylm.asinFactor1Cora i * Taylm.asinDasinCora (i + 1)
      else Taylm.asinFactor1Cora i


-- The model: CORA's code as printed, kept only to be refuted.
/-- The polynomial of the model of `asin x` at the variable `x`, order `k`: the odd terms
`x^i * factor1 / i!` of the loop. -/
noncomputable def Taylm.asinPolyCora (k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    if i % 2 = 1 then x ^ i * Taylm.asinFactor1Cora i / (i.factorial : ℝ) else 0


-- The model: CORA's code as printed, kept only to be refuted.
/-- The upper end of CORA's remainder interval for the variable on `[-r, r]`, order `k`, `k + 1`
even: `r^(k+1) * (asin r)^(k+1) / (k+1)!`. -/
noncomputable def Taylm.asinRemainderUpperCora (k : ℕ) (r : ℝ) : ℝ :=
  r ^ (k + 1) * Real.arcsin r ^ (k + 1) / ((k + 1).factorial : ℝ)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The polynomial at `x = 1`, order `7`. -/
private theorem Taylm.aux_asinPoly_seven_one :
    Taylm.asinPolyCora 7 1 = 1 + 1 / 6 + 3 / 40 + 5 / 112 := by
  simp [Taylm.asinPolyCora, Finset.sum_range_succ, Taylm.asinFactor1Cora,
    Taylm.asinDasinCora, Nat.factorial]
  norm_num


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `x = 1` CORA's enclosure `[p(1), p(1) + R]` misses `asin 1`: its upper end is below. -/
theorem Taylm.asin_remainder_cora_counterexample : -- --- CONCL ---
    Taylm.asinPolyCora 7 1 + Taylm.asinRemainderUpperCora 7 1 < Real.arcsin 1 := by -- --- PROOF ---
  rw [Taylm.aux_asinPoly_seven_one, Taylm.asinRemainderUpperCora, Real.arcsin_one]
  -- `3.14 < π < 3.15`
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  have hp : 0 < Real.pi / 2 := by linarith
  have h3 : (Real.pi / 2) ^ 8 ≤ (1.575 : ℝ) ^ 8 :=
    pow_le_pow_left₀ hp.le (by linarith) 8
  norm_num [Nat.factorial] at h3 ⊢
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
