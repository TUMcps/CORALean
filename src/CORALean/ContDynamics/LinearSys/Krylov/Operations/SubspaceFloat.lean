module

public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.SubspaceFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.OrderOkFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ResidualNormFloat
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The Krylov subspace of a vector with a certified order, in floats

CORA's `priv_subspace_Krylov_individual_Jawecki` with its order test repaired: `ν = ‖c‖`, Arnoldi
for `k₀` passes, then the order `k` is accepted when `orderOkFloat` holds (the computable bound of
`Krylov.error_le_column_residual`, [1, Thm. 3] extended to every matrix, at most `tol` at `t_f`),
else grows by `step` (to at most `n`) until `fuel` tries are out. The result carries the basis,
the Hessenberg entries, the bound and whether it was accepted. Arnoldi is rerun per order; the
passes are the same ones, so CORA.cpp may extend instead.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold
* `A` – matrix
* `c` – start vector
* `k₀` – first order tried
* `step` – growth of the order per try
* `tf` – final time
* `tol` – tolerance
* `fuel` – number of tries

## Output
* order, whether it was accepted, its bound, the scale, the basis and the Hessenberg entries

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

/-- The order search from order `k`: accept it, or stop at `n` or when the fuel is out, or grow by
`step` and rerun Arnoldi. -/
@[step_of Krylov.subspaceFloat]
def Krylov.step_orderSearch (p q : ℕ) (εb : 𝕋) (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (ν μA : 𝕋)
    (step : ℕ) (tf tol : 𝕋) : ℕ → ℕ → Krylov.SubspaceFloat 𝕋 n
  | fuel, k =>
    let st := Krylov.arnoldiFloat p εb A c ν k
    let res := fun j => Krylov.residualNormFloat p A st.1 st.2 j
    let ok := decide (1 ≤ k) && Krylov.orderOkFloat p q μA res c ν st.1 st.2 k tf tol
    let found : Krylov.SubspaceFloat 𝕋 n :=
      ⟨k, ok, Krylov.errorBoundFloat p q μA res c ν st.1 st.2 k tf, ν, st.1, st.2⟩
    match fuel with
    | 0 => found
    | fuel + 1 =>
      if ok || n ≤ k then found
      else Krylov.step_orderSearch p q εb A c ν μA step tf tol fuel (min (k + step) n)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The subspace of `c` under `A`: `ν = ‖c‖`, `μ_A` from Gershgorin, then the order search from
`k₀`. -/
def Krylov.subspaceFloat (p q : ℕ) (εb : 𝕋) (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (k₀ step : ℕ)
    (tf tol : 𝕋) (fuel : ℕ) : Krylov.SubspaceFloat 𝕋 n :=
  let ν := normUp p c
  let μA := Krylov.quadBoundUp A
  Krylov.step_orderSearch p q εb A c ν μA step tf tol fuel (min k₀ n)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
