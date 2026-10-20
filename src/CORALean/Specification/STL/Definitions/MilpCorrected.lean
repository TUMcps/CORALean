module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The program (26) with the strict inequality on the selected row only

The program (26) of [1, Alg. 3, l. 9] decides, for the list of polytopes `⟨C_j, d_j⟩_P` of the
unsafe factors, whether some `α̃ ∈ [-1, 1]^p` lies outside all of them: for each `j` it selects, by
the binaries `λ_jk`, one row `k` that `α̃` violates, `C_j(k,·) α̃ > d_j(k)`, writing `α̃` as the sum
of the `α̃_jk`, `|α̃_jk| ≤ λ_jk`, which are all `0` but the selected one. It is read per `j`.
`C` is the matrix of the rows, `d` the offset, and `a k` the `α̃_jk`.
The corrected program requires `C_j(k,·) α̃_jk > d_j(k)` only where `λ_jk = 1`, which is what the
selection means: the printed one requires it for every `k`, where `λ_jk = 0` forces `α̃_jk = 0`
and the inequality `0 > 0`.

## Inputs
* `C` – constraint matrix
* `d` – offsets
* `α` – factor vector

## Output
* the program is feasible with the strict inequality on the selected row

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {s p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. (26)] with `λ_jk = 1 → C_j(k,·) α̃_jk > d_j(k)`. -/
def STL.milpCorrected (C : Matrix (Fin s) (Fin p) ℝ) (d : Fin s → ℝ) (α : Fin p → ℝ) : Prop :=
  ∃ (a : Fin s → Fin p → ℝ) (lam : Fin s → ℝ),
    (∀ k, lam k = 0 ∨ lam k = 1) ∧ (∀ k, lam k = 1 → d k < ∑ i, C k i * a k i) ∧
    (∀ k i, -lam k ≤ a k i ∧ a k i ≤ lam k) ∧ (∀ i, α i = ∑ k, a k i) ∧ ∑ k, lam k = 1 ∧
    ∀ i, -1 ≤ α i ∧ α i ≤ 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
