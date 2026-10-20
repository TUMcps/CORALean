module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The `H₋` fault-sensitivity inequality, in `(e, f)`

[1, Eq. 25]: `[Φ₁₁ Φ₁₂; ⋆ Φ₂₂] ≺ 0` with `Φ₁₁ = -CᵀMᵀMC + (A - LC)ᵀQ(A - LC) - Q`,
`Φ₁₂ = (A - LC)ᵀQ(-LE) - CᵀMᵀME` and `Φ₂₂ = β²I - EᵀMᵀME + (LE)ᵀQ(LE)`, the blocks sized by the
state and the fault dimension. Stated as its negative being positive definite, the `⋆` block the
transpose of `Φ₁₂`.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – fault matrix
* `L` – observer gain
* `Q` – Lyapunov matrix
* `M` – residual weight
* `β` – sensitivity level

## Output
* the block matrix is negative definite

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

/-- [1, Eq. 25], `≺ 0`. -/
def LinearSysDT.HMinusLmiPhi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf)
    (L : Mat ℝ n ny) (Q : Mat ℝ n n) (M : Mat ℝ ny ny) (β : ℝ) : Prop :=
  let Φ₁₁ : Mat ℝ n n := -(Cᵀ * Mᵀ * M * C) + (A - L * C)ᵀ * Q * (A - L * C) - Q
  let Φ₁₂ : Matrix (Fin n) (Fin nf) ℝ := (A - L * C)ᵀ * Q * (-(L * E)) - Cᵀ * Mᵀ * M * E
  let Φ₂₂ : Mat ℝ nf nf := β ^ 2 • 1 - Eᵀ * Mᵀ * M * E + (L * E)ᵀ * Q * (L * E)
  (-(fromBlocks Φ₁₁ Φ₁₂ Φ₁₂ᵀ Φ₂₂)).PosDef

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
