module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The snapshot matrices of the dynamic mode decomposition with control

The system `x_{k+1} = A x_k + B u_k` [1, Eq. 14] with the snapshots as columns of
`X = [x_1 … x_{m-1}]`, `X' = [x_2 … x_m]` and `Υ = [u_1 … u_{m-1}]` [1, Eq. 15] holds at every
snapshot exactly when `X' = A X + B Υ` [1, Eq. 16], equivalently `X' - B Υ = A X`
[1, Eq. 17], and when `X' = [A B] Ω` for the stacked `Ω = [X; Υ]` [1, Eq. 25]. The matrix
`[A B]` is `dmdcStack A B`, taken apart by `dmdcBlocks`.

## References

* [1] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n l N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The snapshots `f 0, …, f (N - 1)` as the columns of a matrix. -/
def dmdcCols (f : Fin N → Vec ℝ n) : Mat ℝ n N := Matrix.of fun i k => f k i

/-- `[x; u]`, one column of `Ω`. -/
def dmdcRegressor (x : Vec ℝ n) (u : Vec ℝ l) : Vec ℝ (n + l) := Fin.append x u

/-- `[A B]`. -/
def dmdcStack (A : Mat ℝ n n) (B : Mat ℝ n l) : Mat ℝ n (n + l) :=
  Matrix.of fun i j => Fin.addCases (fun a => A i a) (fun b => B i b) j

/-- `(A, B)` from `[A B]`. -/
def dmdcBlocks (G : Mat ℝ n (n + l)) : Mat ℝ n n × Mat ℝ n l :=
  (Matrix.of fun i a => G i (Fin.castAdd l a), Matrix.of fun i b => G i (Fin.natAdd n b))

/-- [1, Eq. 16]: the recursion at every snapshot is `X' = A X + B Υ`. -/
theorem dmdc_data_matrix (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ l) (A : Mat ℝ n n)
    (B : Mat ℝ n l) :
    (∀ k, xNext k = A *ᵥ x k + B *ᵥ u k) ↔
      dmdcCols xNext = A * dmdcCols x + B * dmdcCols u := by -- --- PROOF ---
  constructor
  · intro h
    ext i k
    have := congrFun (h k) i
    simpa [dmdcCols, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using this
  · intro h k
    funext i
    have := congrFun (congrFun h i) k
    simpa [dmdcCols, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using this

/-- [1, Eq. 17]: `X' = A X + B Υ` is `X' - B Υ = A X`. -/
theorem dmdc_data_sub (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ l) (A : Mat ℝ n n)
    (B : Mat ℝ n l) :
    dmdcCols xNext = A * dmdcCols x + B * dmdcCols u ↔
      dmdcCols xNext - B * dmdcCols u = A * dmdcCols x := by
  rw [sub_eq_iff_eq_add, add_comm]

/-- `[A B] [x; u] = A x + B u`. -/
theorem dmdcStack_mulVec (A : Mat ℝ n n) (B : Mat ℝ n l) (x : Vec ℝ n) (u : Vec ℝ l) :
    dmdcStack A B *ᵥ dmdcRegressor x u = A *ᵥ x + B *ᵥ u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, dmdcStack, dmdcRegressor]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The blocks of `[A B]` are `A` and `B`. -/
theorem dmdcBlocks_dmdcStack (A : Mat ℝ n n) (B : Mat ℝ n l) :
    dmdcBlocks (dmdcStack A B) = (A, B) := by
  ext i j <;> simp [dmdcBlocks, dmdcStack]

/-- The blocks act on `[x; u]` as the matrix does. -/
theorem dmdcBlocks_mulVec (G : Mat ℝ n (n + l)) (x : Vec ℝ n) (u : Vec ℝ l) :
    G *ᵥ dmdcRegressor x u = (dmdcBlocks G).1 *ᵥ x + (dmdcBlocks G).2 *ᵥ u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, dmdcBlocks, dmdcRegressor]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- [1, Eq. 25]: `X' = [A B] Ω` for `Ω = [X; Υ]` at every snapshot. -/
theorem dmdc_data_stack (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ l) (A : Mat ℝ n n)
    (B : Mat ℝ n l) : -- --- STMT ---
    (∀ k, xNext k = A *ᵥ x k + B *ᵥ u k) ↔
      dmdcCols xNext =
        dmdcStack A B * dmdcCols (fun k => dmdcRegressor (x k) (u k)) := by -- --- PROOF ---
  constructor
  · intro h
    ext i k
    have := congrFun (h k) i
    rw [← dmdcStack_mulVec] at this
    simpa [dmdcCols, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · intro h k
    funext i
    have := congrFun (congrFun h i) k
    rw [show (dmdcCols (fun k => dmdcRegressor (x k) (u k))) = _ from rfl] at this
    have h2 := congrFun (dmdcStack_mulVec A B (x k) (u k)) i
    simp only [dmdcCols, Matrix.mul_apply, Matrix.of_apply] at this
    simpa [Matrix.mulVec, dotProduct, this] using h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
