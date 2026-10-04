import CORALean.ContDynamics.LinearARX.LinearARX
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# From a state-space model to an ARMAX model, by the characteristic polynomial

CORA's method `'CH'` of `linearSysDT/linearARX` [1]: with `poly(A) = [1, a₁, …, a_n]`, the
coefficients of the characteristic polynomial `x^n + a₁ x^{n-1} + … + a_n`, the model
`x(k+1) = A x(k) + B̃ ũ(k)`, `y(k) = C x(k) + D̃ ũ(k)` has `Ā_i = −a_i I` and
`B̄_i = ∑_{j=0}^{i} a_j CAB_{i-j}` with `CAB₀ = D̃` and `CAB_m = C A^{m-1} B̃`: Cayley-Hamilton
in place of an observer gain, `p = n`. `Abar i` is `Ā_{i+1}` and `Bbar j` is `B̄_j`, as in
`ofObserver`. CORA zeroes the coefficients of `poly(A)` below `1e4 eps`; exact here.

## References

* [1] `contDynamics/@linearSysDT/linearARX.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n dy du : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `A_bar`, `B_bar` of the `'CH'` branch, one coefficient `a_j = coeff (n - j)` at a time. -/
noncomputable def LinearARX.ofCharpoly (A : Mat ℝ n n) (Bu : Mat ℝ n du) (C : Mat ℝ dy n)
    (Du : Mat ℝ dy du) : LinearARX ℝ dy du n where
  Abar i := -(A.charpoly.coeff (n - ((i : ℕ) + 1))) • (1 : Mat ℝ dy dy)
  Bbar j := ∑ i ∈ Finset.range ((j : ℕ) + 1), A.charpoly.coeff (n - i) •
    (if (j : ℕ) - i = 0 then Du else C * A ^ ((j : ℕ) - i - 1) * Bu)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
