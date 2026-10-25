module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The extended input matrices of a NARX linearization

`B_ext,k,i` of [1, Cor. 2]: `B_{k,i} = ∇_{u_{k-i}} h` in the last block row of the window, zero
above. Indexed by an integer because [1, Cor. 2] sums `B_ext,k-j,k-i-j` over shifts that leave
`0 ≤ i ≤ n_p`, and the Jacobian block `B_{k,i}` exists only inside that range; it is read as
zero outside, which the printed formula needs and does not say.

## Inputs
* `np` – number of lags
* `B` – input Jacobian blocks per lag
* `i` – lag index

## Output
* the extended input matrix block at lag `i`

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE Transactions on
      Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ny nu : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Cor. 2]: `B_ext,k,i` for the input Jacobians `B i = B_{k,i}`, zero unless `0 ≤ i ≤ np`. -/
def Conform.narxBext (np : ℕ) (B : ℕ → Mat ℝ ny nu) (i : ℤ) : Mat ℝ (np * ny) nu :=
  Matrix.of fun r c =>
    if 0 ≤ i ∧ i ≤ np ∧ (finProdFinEquiv.symm r).1.val + 1 = np then
      B i.toNat (finProdFinEquiv.symm r).2 c
    else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
