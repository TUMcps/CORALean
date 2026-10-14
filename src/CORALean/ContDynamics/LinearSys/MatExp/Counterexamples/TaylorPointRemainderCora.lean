module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-!
# `MatExp.taylorPointRemainderCora`: the Taylor series of a point matrix as CORA computes it

`@intervalMatrix/private/priv_intervalMatrixRemainder.m` (l. 41-45, 70) starts the remainder `E`
of `priv_taylorSeries`, `priv_hornerTaylorSeries` and `priv_scalingSquaringHornerTaylorSeries`
from the matrix box `[-1, 1]` times `factor`, except for a point matrix:

```
if isequal(intMat.int.sup, intMat.int.inf)
    E = intervalMatrix(ones(n), 0);        % center ones, delta 0: the point ones(n)
else
    E = intervalMatrix(zeros(n), ones(n)); % [-1, 1]
end
...
E = E*factor;
```

`intervalMatrix(C, D)` is `[C - |D|, C + |D|]`, so the point branch adds the constant
`factor * ones(n)` and the result of the series is again a point matrix. One dimension (a
`1 x 1` matrix is a scalar `a`, its
inf-norm `|a|`): the partial sum `∑_{i ≤ m} a^i / i!` plus
`factor = (|a|^(m+1) / (m+1)!) / (1 - |a| / (m+2))`, the result `none` for `m + 2 ≤ |a|` (CORA
returns `[]`). Read from the source, not run.

# CORA's `expmDifferentAlgorithms` of a point matrix is a point that misses `exp(A)`

`expmDifferentAlgorithms(intervalMatrix(-1), 2, 0)` (the Taylor series; style `1`, Horner, has the
same value) gives the partial sum `1 - 1 + 1/2 = 1/2` plus `factor = (1/6) / (3/4) = 2/9`, the
point `13/18`, while `exp(-1) < 1/2`. `expmTaylorHornerScaling` dispatches to the same functions.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `[inf, sup]` of the Taylor series of the `1 x 1` point matrix `a` to order `m`. -/
noncomputable def MatExp.taylorPointRemainderCora (a : ℝ) (m : ℕ) : Option (Interval ℝ) :=
  -- maxOrder + 2 <= alpha
  if (m : ℝ) + 2 ≤ |a| then none
  else
    -- taylor: the partial sum `∑_{i ≤ m} a^i / i!`
    let taylor := ∑ i ∈ Finset.range (m + 1), a ^ i / (i.factorial : ℝ)
    -- factor = prod(alpha ./ (1:m+1)) / (1 - alpha/(maxOrder+2))
    let factor := (|a| ^ (m + 1) / ((m + 1).factorial : ℝ)) / (1 - |a| / ((m : ℝ) + 2))
    -- E = intervalMatrix(ones(n),0) * factor: the point `factor`
    some ⟨taylor + factor, taylor + factor⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `a = -1` and order `2` CORA's result is the point `13/18`, which is above `exp(-1)`. -/
theorem MatExp.taylorPointRemainder_cora_counterexample :
    MatExp.taylorPointRemainderCora (-1) 2 = some ⟨13 / 18, 13 / 18⟩ ∧
      Real.exp (-1) < 13 / 18 := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · simp only [MatExp.taylorPointRemainderCora]
    rw [if_neg (by norm_num [abs_neg])]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · have h1 : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp (by norm_num)
    have h2 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
