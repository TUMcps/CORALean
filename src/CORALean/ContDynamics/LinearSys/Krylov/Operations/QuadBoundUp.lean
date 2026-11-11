module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# An upper bound of the quadratic form of a matrix, in floats

Gershgorin's discs for the symmetric part of `M`: the quadratic form `x*Mx` is at most `μ x*x` for
`μ = max_i (M_{ii} + ½ Σ_{j≠i} (|M_{ij}| + |M_{ji}|))`, every sum and the maximum rounded up. It is
what extends [1, Thm. 3], proved for `W(σA) ⊆ ℂ⁻`, to every matrix: it bounds the growth `‖e^{tM}‖₂
≤ e^{tμ}` of a matrix that is not nonexpansive, in `O(nnz)` for a sparse `M`, `O(k²)` for a
Hessenberg matrix of order `k`. The sums run over `j` from the last index down (`sumUp`), and the
maximum over the rows is seeded at the last row.

## Inputs
* `M` – square matrix

## Output
* upper bound of the matrix's numerical range along the real axis

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max_i (M_{ii} + ½ Σ_{j≠i} (|M_{ij}| + |M_{ji}|))`, rounded up. -/
def Krylov.quadBoundUp (M : Mat 𝕋 k k) : 𝕋 :=
  maximumOver fun i => addUp (M i i) (half (sumUp fun j =>
    if j = i then zero else addUp (absolute (M i j)) (absolute (M j i))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
