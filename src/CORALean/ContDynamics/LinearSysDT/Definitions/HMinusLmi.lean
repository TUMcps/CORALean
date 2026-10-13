module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

/-!
# The `H₋` fault-sensitivity inequality

[1, Eq. 27]: for `α > 0`, `P ≻ 0`, `W`, `Y = MᵀM` and `β`,
`[-αP  αPA - αWC  -αWE; ⋆  -αP - CᵀYC  -CᵀYE; ⋆  ⋆  -EᵀYE + β²I] ≺ 0`, the blocks sized `n_x`,
`n_x` and the fault dimension; it is [1, Eq. 26] at `Q = αP`, `W = PL`, and the gain is
`L = P⁻¹W`. Stated as its negative being positive definite, the `⋆` blocks the transposes.

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nf : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 27], `≺ 0`. -/
def LinearSysDT.HMinusLmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf) (P : Mat ℝ n n)
    (W : Mat ℝ n ny) (Y : Mat ℝ ny ny) (α β : ℝ) : Prop :=
  let R : Matrix (Fin n) (Fin n ⊕ Fin nf) ℝ :=                              -- the first row
    fromCols (α • (P * A) - α • (W * C)) (-(α • (W * E)))
  let D : Matrix (Fin n ⊕ Fin nf) (Fin n ⊕ Fin nf) ℝ :=
    fromBlocks (-(α • P) - Cᵀ * Y * C) (-(Cᵀ * Y * E)) (-(Cᵀ * Y * E))ᵀ (-(Eᵀ * Y * E) + β ^ 2 • 1)
  (-(fromBlocks (-(α • P)) R Rᵀ D)).PosDef

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
