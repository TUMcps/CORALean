module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The regression of sparse identification of nonlinear dynamics

The snapshots are the rows of `X` and `Ẋ` [1, Eq. 4], the library `Θ(X)` [1, Eq. 5] applies
`θ` to every row, and the regression `Ẋ = Θ(X) Ξ` [1, Eq. 7] holds exactly when
`ẋ(t_k) = Ξᵀ Θ(x(t_k)ᵀ)ᵀ` at every snapshot [1, Eq. 9], the column `ξ_i` of `Ξ` giving the
component `ẋ_i = Θ(xᵀ) ξ_i` [1, Eq. 8]. The discrete-time form `X₂ = Θ(X₁) Ξ` [1, Eq. 13]
is the same statement for `x_{k+1}`. For `Θ(x) = x` it is `X₂ᵀ = Ξᵀ X₁ᵀ` and has the same
least-squares cost, the dynamic mode decomposition of `Ξᵀ` [1, Eq. 14].

## Inputs
* `f` – snapshot function

## Output
* the snapshots as the rows of a matrix

## References

* [1] S. L. Brunton, J. L. Proctor and J. N. Kutz. "Discovering governing equations from data by
      sparse identification of nonlinear dynamical systems". Proceedings of the National
      Academy of Sciences, 113(15):3932-3937, 2016 (arXiv:1509.03580).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The snapshots `f 0, …, f (m - 1)` as the rows of a matrix. -/
def sindyRows (f : Fin m → Vec ℝ n) : Mat ℝ m n := Matrix.of fun k i => f k i

/-- `Θ(X)`: the library `θ` at every snapshot. -/
def sindyTheta (θ : Vec ℝ n → Vec ℝ p) (x : Fin m → Vec ℝ n) : Mat ℝ m p :=
  sindyRows fun k => θ (x k)

/-- `f(x) = Ξᵀ Θ(xᵀ)ᵀ`. -/
def sindyModel (θ : Vec ℝ n → Vec ℝ p) (Ξ : Mat ℝ p n) (x : Vec ℝ n) : Vec ℝ n :=
  Ξᵀ *ᵥ θ x

/-- [1, Eq. 8]: `ẋ_i = Θ(xᵀ) ξ_i`. -/
theorem sindyModel_apply (θ : Vec ℝ n → Vec ℝ p) (Ξ : Mat ℝ p n) (x : Vec ℝ n) (i : Fin n) :
    sindyModel θ Ξ x i = ∑ j, θ x j * Ξ j i := by
  simp [sindyModel, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

/-- [1, Eq. 7], [1, Eq. 9] and [1, Eq. 13]: `Y = Θ(X) Ξ` holds iff the model `f` of
[1, Eq. 9] gives every row of `Y` (`Y = Ẋ` or `X₂`). -/
theorem sindy_data_iff (θ : Vec ℝ n → Vec ℝ p) (x y : Fin m → Vec ℝ n)
    (Ξ : Mat ℝ p n) : -- --- CONCL ---
    sindyRows y = sindyTheta θ x * Ξ ↔ ∀ k, y k = sindyModel θ Ξ (x k) := by -- --- PROOF ---
  constructor
  · intro h k
    funext i
    have := congrFun (congrFun h k) i
    rw [sindyModel_apply]
    simpa [sindyRows, sindyTheta, Matrix.mul_apply] using this
  · intro h
    ext k i
    have := congrFun (h k) i
    rw [sindyModel_apply] at this
    simpa [sindyRows, sindyTheta, Matrix.mul_apply] using this

/-- [1, Eq. 14]: for a linear library `X₂ = X₁ Ξ` is `X₂ᵀ = Ξᵀ X₁ᵀ`, with the same squared
error for every `Ξ`: a least-squares `Ξ` is the dynamic mode decomposition `Ξᵀ`. -/
theorem sindy_linear_transpose (X₁ X₂ : Mat ℝ m n) (Ξ : Mat ℝ n n) : -- --- CONCL ---
    (X₂ = X₁ * Ξ ↔ X₂ᵀ = Ξᵀ * X₁ᵀ) ∧
      ∑ k, ∑ i, ((X₂ - X₁ * Ξ) k i) ^ 2
        = ∑ i, ∑ k, ((X₂ᵀ - Ξᵀ * X₁ᵀ) i k) ^ 2 := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · rw [← Matrix.transpose_mul]
    exact ⟨fun h => by rw [h], fun h => by simpa using congrArg Matrix.transpose h⟩
  · rw [← Matrix.transpose_mul, ← Matrix.transpose_sub]
    simp only [Matrix.transpose_apply]
    exact Finset.sum_comm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
