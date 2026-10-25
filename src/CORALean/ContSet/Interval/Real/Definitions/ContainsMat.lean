module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.ContainsMat`

CORA's `@intervalMatrix/contains` with `type = 'exact'`: column by column, `interval/contains_`
on a numeric column. A column that is empty contains nothing. Otherwise every entry must satisfy
`inf < M + tol` and `sup > M - tol`, or be within `tol` of that bound by `IsWithinTol`, which is
`|a - b| <= tol` or `|a - b| / min(|a|, |b|) <= tol`; the quotient is written as a product, which
differs only at `min = 0`, where the absolute test decides anyway.

## Inputs
* `A` – interval matrix
* `M` – real matrix
* `tol` – tolerance

## Output
* `M` lies in `A` up to the tolerance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contains(intMat, M, 'exact', tol)`: `M` is in the box up to the tolerance `tol`. -/
def Interval.ContainsMat (A : Interval (Mat ℝ m n)) (M : Mat ℝ m n) (tol : ℝ) : Prop :=
  let within : ℝ → ℝ → Prop := fun a b => |a - b| ≤ tol ∨ |a - b| ≤ tol * min |a| |b|
  ∀ j, (∀ i, A.inf i j ≤ A.sup i j) ∧ ∀ i,
    (A.inf i j < M i j + tol ∨ within (A.inf i j) (M i j)) ∧
    (M i j - tol < A.sup i j ∨ within (A.sup i j) (M i j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
