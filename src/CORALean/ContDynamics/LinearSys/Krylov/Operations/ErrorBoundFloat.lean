module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.DecayProductFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.QuadBoundUp
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.StartErrorFloat
public import CORALean.Global.Float.Exp

@[expose] public section

/-!
# A computable bound of the Krylov error for every matrix, in floats

`‖e^{tA}c - ν V_k e^{tT_k}e₁‖₂ ≤ e^{tμ}(|ν|(|τ|‖w‖|γ| t^k/k! + (Σ_j ε_j) t) + ρ)`
(`Krylov.error_le_column_residual`, [1, Thm. 3] with the growth rate and the residuals added),
rounded up: `μ = max(0, μ_A, μ_T)` from Gershgorin's discs (so `e^{tμ} = 1` for [1]'s nonexpansive
case), `ε_j` the column residuals of the stored basis, `ρ` the distance of `ν v(1)` from `c`, the
decay product by ratios (`decayProductFloat`) so that no factorial is formed. The discs of `A`
are computed once per matrix, `T_k`'s in `O(k²)`.

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

## Output
* upper bound of the Krylov error over `[0, t]`

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

/-- `e^{tμ}(|ν|(‖w‖ Π_{j ≤ k}|h_{j+1,j}|t/j + (Σ_{j<k} ε_j) t) + ρ)`, `μ = max(0, μA, μ_{T_k})`. -/
def Krylov.errorBoundFloat (p q : ℕ) (μA : 𝕋) (ε : ℕ → 𝕋) (c : Vec 𝕋 n) (ν : 𝕋)
    (V : ℕ → Vector 𝕋 n) (H : ℕ → ℕ → 𝕋) (k : ℕ) (t : 𝕋) : 𝕋 :=
  -- the growth rate `μ`
  let μT := Krylov.quadBoundUp fun i j : Fin k => H i j
  let μ := maximum zero (maximum μA μT)
  -- the decay product `‖w‖ Π_{j ≤ k} |h_{j+1,j}| t / j`
  let wn := normUp p fun l : Fin n => (V k)[l]
  let decay := Krylov.decayProductFloat wn t H k
  -- the residuals' share, and the start vector's error
  let S := sumUp fun j : Fin k => ε j
  let ρ := Krylov.startErrorFloat p c ν (V 0)
  mulUp (expUp q (mulUp t μ)) (addUp (mulUp (absolute ν) (addUp decay (mulUp S t))) ρ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
