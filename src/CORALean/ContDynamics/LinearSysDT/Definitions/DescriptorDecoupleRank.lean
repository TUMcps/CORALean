module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

/-!
# The decoupling rank condition of the descriptor system

[1, Eq. 6]: for `E`, `D_d` and `C` the matrices of `E x₊ = A x + B u + D ω + D_d d`, `y = C x + F
υ`, `rank [I_{n_x} ⊗ [E D_d; C 0]; vec([I_{n_x}; 0])ᵀ] = n_x · rank [E D_d; C 0]`: the row
`vec([I; 0])ᵀ` stacked under the Kronecker product `I ⊗ [E D_d; C 0]` adds no rank. `vec` stacks
the columns, as in Mathlib, and `⊗` is the Kronecker product with the identity on the left.
## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Kronecker

variable {nx ny nd : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 6]: the rank condition under which the unknown input can be decoupled. -/
def LinearSysDT.DescriptorDecoupleRank (E : Mat ℝ nx nx) (Dd : Mat ℝ nx nd) (C : Mat ℝ ny nx) :
    Prop :=
  let M : Matrix (Fin nx ⊕ Fin ny) (Fin nx ⊕ Fin nd) ℝ := fromBlocks E Dd C 0     -- [E D_d; C 0]
  let J : Matrix (Fin nx ⊕ Fin nd) (Fin nx) ℝ := fromRows 1 0                      -- [I; 0]
  (fromRows ((1 : Matrix (Fin nx) (Fin nx) ℝ) ⊗ₖ M) (Matrix.replicateRow Unit (vec J))).rank =
    nx * M.rank

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
