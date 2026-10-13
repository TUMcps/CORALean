module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

/-!
# The `H₋` fault-sensitivity inequality, with the gain

[1, Eq. 26]: `[-Q  QA - QLC  -QLE; ⋆  -Q - CᵀMᵀMC  -CᵀMᵀME; ⋆  ⋆  -EᵀMᵀME + β²I] ≺ 0`, the
blocks sized `n_x`, `n_x` and the fault dimension; it is [1, Eq. 25] by the Schur complement of
the block `-Q`. Stated as its negative being positive definite, the `⋆` blocks the transposes.

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nf : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 26], `≺ 0`. -/
def LinearSysDT.HMinusLmiGain (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf)
    (L : Mat ℝ n ny) (Q : Mat ℝ n n) (M : Mat ℝ ny ny) (β : ℝ) : Prop :=
  let R : Matrix (Fin n) (Fin n ⊕ Fin nf) ℝ :=                              -- the first row
    fromCols (Q * A - Q * L * C) (-(Q * L * E))
  let D : Matrix (Fin n ⊕ Fin nf) (Fin n ⊕ Fin nf) ℝ :=
    fromBlocks (-Q - Cᵀ * Mᵀ * M * C) (-(Cᵀ * Mᵀ * M * E)) (-(Cᵀ * Mᵀ * M * E))ᵀ
      (-(Eᵀ * Mᵀ * M * E) + β ^ 2 • 1)
  (-(fromBlocks (-Q) R Rᵀ D)).PosDef

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
