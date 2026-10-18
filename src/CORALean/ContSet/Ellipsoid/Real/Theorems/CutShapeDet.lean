module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.CutShape
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The determinant of the cut ellipsoid's shape matrix

For a unit `c`, `det(a(I − κ c cᵀ)) = aⁿ (1 − κ)`, as `det(I − κ c cᵀ) = 1 − κ cᵀc` (the
Weinstein-Aronszajn identity), and the `ⁿ` is that of `det(a M) = aⁿ det M` for an `n × n` matrix
`M`. For the matrix `E = a (I − κ c cᵀ)` of [1, Eq. 16], `a = n(1 − γ²)/(n − 1)` and
`κ = (1 − nγ²)/(1 − γ²)`, that is `(n(1 − γ²)/(n − 1))ⁿ · (1 − (1 − nγ²)/(1 − γ²))`, the square of
the volume ratio that [1, Lemma 4.4] bounds. The paper does not print this determinant; it is what
the proof of the lemma needs.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_det_one_sub (c : Vec ℝ n) (κ : ℝ) (hc : c ⬝ᵥ c = 1) :
    (1 - κ • vecMulVec c c : Mat ℝ n n).det = 1 - κ := by -- --- PROOF ---
  have : (κ • vecMulVec c c : Mat ℝ n n)
      = replicateCol (Fin 1) (κ • c) * replicateRow (Fin 1) c := by
    rw [vecMulVec_eq (Fin 1)]
    ext i j
    simp [Matrix.mul_apply]
    ring
  rw [this, det_one_sub_mul_comm]
  simp only [Matrix.det_unique, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, Pi.smul_apply, smul_eq_mul]
  have h : ∑ x, c x * (κ * c x) = κ * (c ⬝ᵥ c) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, hc, mul_one]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The determinant of [1, Eq. 16]'s `E`, used in the proof of [1, Lemma 4.4]:
`det E = (n(1 − γ²)/(n − 1))ⁿ (1 − (1 − nγ²)/(1 − γ²))`, the `ⁿ` being `det(a M) = aⁿ det M` for
`n × n`. -/
theorem Ellipsoid.cutShape_det {c : Vec ℝ n} (hc : c ⬝ᵥ c = 1) (γ : ℝ) :
    (Ellipsoid.cutShape n c γ).det
      = ((n : ℝ) * (1 - γ ^ 2) / ((n : ℝ) - 1)) ^ n
        * (1 - (1 - (n : ℝ) * γ ^ 2) / (1 - γ ^ 2)) := by
  unfold Ellipsoid.cutShape
  rw [det_smul, Ellipsoid.aux_det_one_sub c _ hc, Fintype.card_fin]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
