module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

/-!
# The `H∞` observer-design inequality

Eq. 16 of [1, Thm. 1]: for `γ > 0`, `P ≻ 0` and `Y`,
`[I - P ⋆ ⋆ ⋆; 0 -γ²I ⋆ ⋆; 0 0 -γ²I ⋆; PA - YC  PE  -YF  -P] ≺ 0`, the blocks sized
`n_x, n_w, n_v, n_x`; the gain is `L = P⁻¹ Y`. Stated as its negative being positive definite.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – disturbance matrix
* `F` – noise matrix
* `P` – Lyapunov matrix
* `Y` – gain variable
* `γ` – attenuation level

## Output
* the block matrix is negative definite

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. 16 of [1, Thm. 1], `≺ 0`. -/
def LinearSysDT.HinfLmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw) (F : Mat ℝ ny nv)
    (P : Mat ℝ n n) (Y : Mat ℝ n ny) (γ : ℝ) : Prop :=
  let TL : Matrix (Fin n ⊕ (Fin nw ⊕ Fin nv)) (Fin n ⊕ (Fin nw ⊕ Fin nv)) ℝ :=
    fromBlocks (1 - P) 0 0 (fromBlocks (-(γ ^ 2) • 1) 0 0 (-(γ ^ 2) • 1))
  let R : Matrix (Fin n) (Fin n ⊕ (Fin nw ⊕ Fin nv)) ℝ :=
    fromCols (P * A - Y * C) (fromCols (P * E) (-(Y * F)))
  (-(fromBlocks TL Rᵀ R (-P))).PosDef

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
