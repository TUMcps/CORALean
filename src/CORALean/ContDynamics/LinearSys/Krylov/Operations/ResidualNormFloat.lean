module

public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The residual of a computed Arnoldi column, bounded in floats

The Krylov identity of [1, Eq. 2.2] holds for a computed basis and Hessenberg matrix up to the
residual `δ(j)`, entry `r`: `(A v(j))_r - Σ_{i ≤ j+1} h_{i,j} v(i)_r`. Each entry is enclosed by
a product and a sum rounded each way (`lo`, `hi`) and the column's Euclidean norm is bounded from
above by `normUp` of the larger of `|lo|`, `|hi|`. Nothing about `V` or `H` is assumed: not
orthogonality, not that they come from an Arnoldi iteration.

## Inputs
* `p` – Newton steps per norm
* `A` – matrix
* `V` – basis vectors
* `H` – Hessenberg entries
* `j` – column

## Output
* upper bound of the Euclidean norm of the column's residual

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

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Entry `r` of the residual's magnitude bound: `max(|lo|, |hi|)` of `(A v(j))_r - Σ_{i ≤ j+1}
h_{i,j} v(i)_r`, each term and sum rounded the way that bounds it. -/
@[step_of Krylov.residualNormFloat]
def Krylov.step_residualColumn (A : Mat 𝕋 n n) (V : ℕ → Vector 𝕋 n) (H : ℕ → ℕ → 𝕋) (j : ℕ) :
    Vec 𝕋 n := fun r =>
  let vj : Vec 𝕋 n := fun l => (V j)[l]
  let lo := subDown (dotDown (A r) vj) (sumUp fun i : Fin (j + 2) => mulUp (H i j) (V i)[r])
  let hi := subUp (dotUp (A r) vj) (sumDown fun i : Fin (j + 2) => mulDown (H i j) (V i)[r])
  maximum (absolute lo) (absolute hi)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Euclidean norm of the column's residual, from above. -/
def Krylov.residualNormFloat (p : ℕ) (A : Mat 𝕋 n n) (V : ℕ → Vector 𝕋 n) (H : ℕ → ℕ → 𝕋)
    (j : ℕ) : 𝕋 :=
  normUp p (Krylov.step_residualColumn A V H j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
