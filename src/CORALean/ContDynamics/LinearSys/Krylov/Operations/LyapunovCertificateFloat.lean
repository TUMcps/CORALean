module

public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.LyapunovCertificateFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.QuadBoundUp

@[expose] public section

/-!
# A checked Lyapunov weight of a matrix, in floats

A weight `P` for which `A*P + PA = -I` holds only approximately is certified, not trusted
([1, Eq. 3.4] needs a bound of the growth). A float `P` and a factor `L` of `P - aI` (Cholesky, from
anywhere) are checked with outward roundings: `E = P - aI - L*L` and `W = PA + (PA)* + I` are
bounded entrywise, and Gershgorin's `quadBoundUp` of the bounds gives `x*Px ≥ (a - ρ_E)x*x` and
`x*PAx ≤ -½(1 - ρ_W)x*x`. The weight is accepted when `P` is symmetric and `a - ρ_E`, `1 - ρ_W`,
`b = quadBoundUp P` are positive; then `μ = -(1 - ρ_W)/(2b)` is a rate. Cost: the products `L*L` and
`PA`, `O(n³)` once per system, `PA` in `O(n nnz(A))` for a sparse `A`.

## Inputs
* `A` – matrix
* `P` – symmetric weight
* `L` – factor of `P - aI`
* `a` – shift

## Output
* the weight with its bounds, rate and acceptance

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Accepts `P` if symmetric and `quadBoundUp` bounds `|P - aI - L*L|` and `|PA + (PA)* + I|` below
`a` and `1`; `lower = a - ρ_E`, `upper = quadBoundUp P`, `rate = -(1 - ρ_W)/(2 upper)`. -/
def Krylov.lyapunovCertificateFloat (A P L : Mat 𝕋 n n) (a : 𝕋) :
    Krylov.LyapunovCertificateFloat 𝕋 :=
  -- `L*L` between its rounded-down and rounded-up product
  let Lt : Mat 𝕋 n n := fun i j => L j i
  let LLdn := matMulDown Lt L
  let LLup := matMulUp Lt L
  -- the entries of `E = P - aI - L*L`, bounded in absolute value, and the bound of `x*Ex`
  let CE : Mat 𝕋 n n := fun i j =>
    let d := if i = j then a else zero
    maximum (absolute (subDown (subDown (P i j) d) (LLup i j)))
      (absolute (subUp (subUp (P i j) d) (LLdn i j)))
  let ρE := Krylov.quadBoundUp CE
  let lower := subDown a ρE
  let upper := Krylov.quadBoundUp P
  -- `PA` between its rounded-down and rounded-up product
  let PAdn := matMulDown P A
  let PAup := matMulUp P A
  -- the entries of `W = PA + (PA)* + I`, bounded in absolute value, and the bound of `x*Wx`
  let CW : Mat 𝕋 n n := fun i j =>
    let d := if i = j then one else zero
    maximum (absolute (addDown (addDown (PAdn i j) (PAdn j i)) d))
      (absolute (addUp (addUp (PAup i j) (PAup j i)) d))
  let ρW := Krylov.quadBoundUp CW
  let gap := subDown one ρW
  let rate := neg (divDown gap (addUp upper upper))
  let symmetric := decide (∀ i j : Fin n, le (P i j) (P j i) = true ∧ le (P j i) (P i j) = true)
  ⟨symmetric && ltStrict zero lower && ltStrict zero gap && ltStrict zero upper, lower, upper, rate⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
