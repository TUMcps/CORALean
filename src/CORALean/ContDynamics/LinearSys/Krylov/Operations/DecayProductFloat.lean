module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The decay product `|τ|‖w‖|γ| t^k/k!` of the Krylov error, without a factorial

`‖w‖ Π_{j=1}^{k} (|h_{j+1,j}| t / j)`, the factor of [1, Thm. 3] that decays with the order, as the
running product `acc_{j} = acc_{j-1} · |h_{j+1,j}| · t / j` (multiplied by `|h|`, then by `t`, then
divided, each rounded up), with `acc_0 = ‖w‖`. `t^k` and `k!` never appear on their own, so that
neither overflows where the quotient does not (CORA's `k!` is infinite from `k = 171` on and its
bound then reads `0`). The divisor is `j` rounded down and floored at one.

## Inputs
* `wn` – upper bound of the norm of the next vector
* `t` – time
* `H` – Hessenberg entries

## Output
* upper bound of the product after `k` factors

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

/-- `acc_k` for `acc_0 = wn`, `acc_{j+1} = acc_j · |h_{j+2,j+1}| · t / (j + 1)`; `H i j` is
`h_{i+1,j+1}`. -/
def Krylov.decayProductFloat (wn t : 𝕋) (H : ℕ → ℕ → 𝕋) : ℕ → 𝕋
  | 0 => wn
  | j + 1 => divUp (mulUp (mulUp (Krylov.decayProductFloat wn t H j) (absolute (H (j + 1) j))) t)
      (maximum one (nsmulDown (j + 1) one))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
