import CORALean.ContDynamics.LinearSys.Krylov.Operations.GramSchmidtStep
import CORALean.Global.EuclideanNorm

/-!
# The Arnoldi iteration

[1, Alg. 1] after `k` passes: the vectors `v(1), …, v(k+1)` at indices `0, …, k`, and the
Hessenberg entries `h_{i,j}` at `(i - 1, j - 1)`. Line 1 normalizes `v`; each pass takes
`w = C v(k)` (line 3), sweeps it against the earlier vectors (lines 4–7), and stores
`h_{k+1,k} = ‖w‖` and `v(k+1) = w / h_{k+1,k}` (lines 8 and 12). The happy breakdown of
lines 9–11 stops the loop, which here is the caller stopping at `ξ = k`: only passes with
`h_{k+1,k} ≠ 0` are read. Over ℝ, the norm the Euclidean one.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Krylov.arnoldi (C : Mat ℝ n n) (v : Vec ℝ n) :
    ℕ → (ℕ → Vec ℝ n) × (ℕ → ℕ → ℝ)
  | 0 => (fun _ => ‖v‖₂⁻¹ • v, fun _ _ => 0)
  | k + 1 =>
    let prev := Krylov.arnoldi C v k
    let V := prev.1
    let w := C *ᵥ V k
    let swept := Krylov.gramSchmidtStep w V (k + 1)
    let hnext := ‖swept.1‖₂
    (Function.update V (k + 1) (hnext⁻¹ • swept.1),
      fun i j => if j = k then (if i ≤ k then swept.2 i else if i = k + 1 then hnext else 0)
        else prev.2 i j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
