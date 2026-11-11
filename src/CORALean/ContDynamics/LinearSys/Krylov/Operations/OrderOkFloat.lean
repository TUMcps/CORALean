module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ErrorBoundFloat

@[expose] public section

/-!
# The order test of the Krylov error bound, in floats

Whether order `k` meets the tolerance `tol` at time `t`: `tμ` within the range `expUp` is sound for
(`≤ 2^q/2`, tested against `nsmulDown (2^{q-1}) one`) and `Krylov.errorBoundFloat` at most `tol`.
Where CORA tests `ν τ γ t^k/k! ≤ tol` ([1, Thm. 3], valid for a nonexpansive `A` only), this accepts
an order only when the error of the stored basis is under `tol` (`Krylov.subspaceFloat_error_le`).

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `μA` – upper bound of the quadratic form of `A`
* `ε` – bounds of the residual norms
* `c` – start vector
* `ν` – its norm
* `V` – basis vectors
* `H` – Hessenberg entries
* `k` – order
* `t` – time
* `tol` – tolerance

## Output
* whether the order is accepted

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether `tμ` is within `expUp`'s range and the bound of order `k` at `t` is at most `tol`. -/
def Krylov.orderOkFloat (p q : ℕ) (μA : 𝕋) (ε : ℕ → 𝕋) (c : Vec 𝕋 n) (ν : 𝕋)
    (V : ℕ → Vector 𝕋 n) (H : ℕ → ℕ → 𝕋) (k : ℕ) (t tol : 𝕋) : Bool :=
  let μT := Krylov.quadBoundUp fun i j : Fin k => H i j
  let μ := maximum zero (maximum μA μT)
  le (mulUp t μ) (nsmulDown (2 ^ (q - 1)) one) &&
    le (Krylov.errorBoundFloat p q μA ε c ν V H k t) tol

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
