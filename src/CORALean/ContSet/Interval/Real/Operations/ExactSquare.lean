module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.exactSquare`

CORA's `@intervalMatrix/exactSquare`, entry by entry as its loop writes it: off the diagonal
`A i j (A i i + A j j) + ∑_{k ≠ i, j} A i k A k j`, on it `A i i ^ 2 + ∑_{k ≠ i} A i k A k i`.
Every matrix entry occurs once in each such expression, apart from the square of `A i i`, which
is the interval power, so interval arithmetic loses nothing (`Theorems/ExactSquareEntryExact`).
No reference is cited: the printed algorithm is in `matrixSet/@intervalMatrix/exactSquare.m`.

## Inputs
* `A` – interval matrix

## Output
* entrywise range of the matrix square over the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `exactSquare`: the entrywise range of `M * M` over the box, built from `mulLo`/`mulHi`
with the squared diagonal entry as the interval power `.^2`; the off-diagonal sum is over
`k ≠ i, j` and the diagonal one over `k ≠ i`. -/
noncomputable def Interval.exactSquare (A : Interval (Mat ℝ n n)) : Interval (Mat ℝ n n) where
  inf := fun i j =>
    if i = j then
      (if A.inf i i < 0 ∧ 0 < A.sup i i then 0 else min (A.inf i i ^ 2) (A.sup i i ^ 2))
        + ∑ k ∈ Finset.univ.erase i,
          Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i)
    else
      Interval.mulLo (A.inf i j) (A.sup i j) (A.inf i i + A.inf j j) (A.sup i i + A.sup j j)
        + ∑ k ∈ Finset.univ \ {i, j},
          Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
  sup := fun i j =>
    if i = j then
      max (A.inf i i ^ 2) (A.sup i i ^ 2)
        + ∑ k ∈ Finset.univ.erase i,
          Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i)
    else
      Interval.mulHi (A.inf i j) (A.sup i j) (A.inf i i + A.inf j j) (A.sup i i + A.sup j j)
        + ∑ k ∈ Finset.univ \ {i, j},
          Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
