module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# The strict Schur complement

A positive definite block matrix `[A  B; Bᵀ  D]` with `D ≻ 0` has `A - B D⁻¹ Bᵀ ≻ 0`: the
direction the linear matrix inequalities of the observer papers are read in, from the block
form a solver certifies to the quadratic form a proof needs. Mathlib has the semidefinite
equivalence (`Matrix.PosDef.fromBlocks₂₂`); the strict half is the quadratic form of the
block matrix at `(x, -D⁻¹ Bᵀ x)`, which is `xᵀ (A - B D⁻¹ Bᵀ) x` by
`Matrix.schur_complement_eq₂₂` and nonzero with `x`.

## Inputs
* `A` – upper left block
* `B` – off-diagonal block
* `D` – lower right block

## Hypotheses
* `hD` – the lower right block is positive definite
* `h` – the block matrix is positive definite

## Conclusion
* the Schur complement is positive definite
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m k : Type} [Fintype m] [Fintype k] [DecidableEq k]


-- =======================================  MAIN THEOREM  ======================================= --

theorem posDef_schur_of_fromBlocks (A : Matrix m m ℝ) (B : Matrix m k ℝ) {D : Matrix k k ℝ}
    (hD : D.PosDef) (h : (fromBlocks A B Bᵀ D).PosDef) :
    (A - B * D⁻¹ * Bᵀ).PosDef := by -- --- PROOF ---
  haveI : Invertible D := hD.isUnit.invertible
  have hB : Bᴴ = Bᵀ := conjTranspose_eq_transpose_of_trivial B
  have hpsd := (PosDef.fromBlocks₂₂ A B hD).mp (by rw [hB]; exact h.posSemidef)
  rw [hB] at hpsd
  refine posDef_iff_dotProduct_mulVec.mpr ⟨hpsd.1, fun x hx => ?_⟩
  -- the block form at `(x, -D⁻¹ Bᵀ x)`
  have hw : (x ⊕ᵥ (-((D⁻¹ * Bᵀ) *ᵥ x))) ≠ 0 := by
    intro h0
    exact hx (funext fun i => by simpa using congrFun h0 (Sum.inl i))
  have hpos := (posDef_iff_dotProduct_mulVec.mp h).2 hw
  rw [dotProduct_mulVec, ← hB, schur_complement_eq₂₂ A B _ _ hD.isHermitian, hB] at hpos
  simpa [dotProduct_mulVec] using hpos

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
