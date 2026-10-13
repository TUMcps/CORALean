module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The program (26) as printed

The program (26) of [1, Alg. 3, l. 9] decides, for the list of polytopes `⟨C_j, d_j⟩_P` of the
unsafe factors, whether some `α̃ ∈ [-1, 1]^p` lies outside all of them: for each `j` it selects, by
the binaries `λ_jk`, one row `k` that `α̃` violates, `C_j(k,·) α̃ > d_j(k)`, writing `α̃` as the sum
of the `α̃_jk`, `|α̃_jk| ≤ λ_jk`, which are all `0` but the selected one. It is read per `j`.
`C` is the matrix of the rows, `d` the offset, and `a k` the `α̃_jk`.
It is as printed: `C_j(·,k) α̃_jk > λ_jk d_j(k)` for every `k`, the strict inequality included,
with the column `(·,k)` of the notation of [1, Sec. 2.1] read as the row `k`, which is its
meaning.

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

/-- [1, Eq. (26)] as printed: the constraints of one polytope, `lam` the binaries `λ_jk`. -/
def STL.milpPrinted (C : Matrix (Fin s) (Fin p) ℝ) (d : Fin s → ℝ) (α : Fin p → ℝ) : Prop :=
  ∃ (a : Fin s → Fin p → ℝ) (lam : Fin s → ℝ),
    (∀ k, lam k = 0 ∨ lam k = 1) ∧ (∀ k, lam k * d k < ∑ i, C k i * a k i) ∧
    (∀ k i, -lam k ≤ a k i ∧ a k i ≤ lam k) ∧ (∀ i, α i = ∑ k, a k i) ∧ ∑ k, lam k = 1 ∧
    ∀ i, -1 ≤ α i ∧ α i ≤ 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
