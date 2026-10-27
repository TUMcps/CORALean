module

public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamAMul
public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamAMulVec

@[expose] public section

/-!
# Partial solve zeroes row `r`

[1, Sec. 4.2]: with `Λ_A` of eq. 29, `[Ã | b̃]` has an identically zero `r`-th row (the paper's
first), the trivial constraint `0ᵀξ = 0` from substituting eq. 28 into row `r`.

## Inputs
* `q` – number of constraints
* `h` – number of generators
* `A` – constraint matrix
* `b` – constraint offset
* `r` – constraint row to solve
* `j` – coefficient to eliminate

## Hypotheses
* `hAj` – pivot entry nonzero

## Conclusion
* the constraint row r of the partial solve is zero

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: after eq. 29, row `r` of `[Ã | b̃]` is the trivial `0ᵀξ = 0`. -/
theorem ConZonotope.partialSolve_zero_row {q h : ℕ} (A : Mat ℝ q h) (b : Vec ℝ q)
    (r : Fin q) (j : Fin h) (hAj : A r j ≠ 0) : -- --- CONCL ---
    (∀ l, (A - ConZonotope.partialSolveΛA A r j * A) r l = 0) ∧
      (b - ConZonotope.partialSolveΛA A r j *ᵥ b) r = 0 := by -- --- PROOF ---
  refine ⟨fun l => ?_, ?_⟩
  · rw [Matrix.sub_apply, ConZonotope.partialSolveΛA_mul]
    field_simp
    ring
  · rw [Pi.sub_apply, ConZonotope.partialSolveΛA_mulVec]
    field_simp
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
