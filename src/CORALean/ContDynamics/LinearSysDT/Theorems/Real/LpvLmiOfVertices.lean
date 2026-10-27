module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.Global.DoubleSumPosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators

@[expose] public section

/-!
# The vertex conditions of the LPV estimator, corrected

[1, Cor. 2]: the matrix inequality Eq. 19 of [1, Thm. 2] at the scheduled
`A(θ) = Σⱼ ρⱼ Aⱼ`, `D(θ)` alike and `Λ(θ) = Σᵢ ρᵢ Λᵢ`, `Yᵢ = PΛᵢ`, is `Σᵢ Σⱼ ρᵢρⱼ Ψᵢⱼ` with the
vertex matrices `Ψᵢⱼ` of its Eq. 30, so it follows from [1, Lemma 2] at `Γ = Ψ`. The corollary
prints the lemma's condition (its Eq. 29b) for `i < j` and with `≽`, which fails
(`lpvLmi_of_vertices_counterexample`); here it is strict and for every ordered pair `i ≠ j`
(`doubleSum_posDef`). The weights need `ρ ≥ 0`, `Σ ρ = 1` [1, Eq. 2], and `P` is symmetric.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `C` – output matrix
* `F` – noise matrix
* `P` – Lyapunov matrix
* `Λ` – vertex gains
* `Y` – vertex gain variables
* `A` – vertex state matrices
* `D` – vertex disturbance matrices
* `α` – first scaling
* `β` – second scaling
* `ρ` – vertex weights

## Hypotheses
* `hρ0` – weights nonnegative
* `hρ1` – weights sum to one
* `hPT` – Lyapunov matrix symmetric
* `hY` – gain variables equal the Lyapunov matrix times the gains

## Conclusion
* the vertex conditions imply the estimator inequality at the scheduled matrices

## References

* [1] [Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      2019.](../../../../../../references/2019/wang-tac-descriptor-lpv-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nd r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- a weighted double sum of block matrices is the block matrix of the sums
private theorem LinearSysDT.aux_sum_fromBlocks {a b c d : Type} [Fintype a] [Fintype b] [Fintype c]
    [Fintype d] (w : Fin r → Fin r → ℝ) (M₁ : Fin r → Fin r → Matrix a c ℝ)
    (M₂ : Fin r → Fin r → Matrix a d ℝ) (M₃ : Fin r → Fin r → Matrix b c ℝ)
    (M₄ : Fin r → Fin r → Matrix b d ℝ) : -- --- CONCL ---
    ∑ i, ∑ j, w i j • fromBlocks (M₁ i j) (M₂ i j) (M₃ i j) (M₄ i j) =
      fromBlocks (∑ i, ∑ j, w i j • M₁ i j) (∑ i, ∑ j, w i j • M₂ i j)
        (∑ i, ∑ j, w i j • M₃ i j) (∑ i, ∑ j, w i j • M₄ i j) := by -- --- PROOF ---
  ext (x | x) (y | y) <;> simp [Matrix.sum_apply, fromBlocks]

-- the same for columns
private theorem LinearSysDT.aux_sum_fromCols {a c d : Type} [Fintype c] [Fintype d]
    (w : Fin r → Fin r → ℝ) (M₁ : Fin r → Fin r → Matrix a c ℝ)
    (M₂ : Fin r → Fin r → Matrix a d ℝ) : -- --- CONCL ---
    ∑ i, ∑ j, w i j • fromCols (M₁ i j) (M₂ i j) =
      fromCols (∑ i, ∑ j, w i j • M₁ i j) (∑ i, ∑ j, w i j • M₂ i j) := by -- --- PROOF ---
  ext x (y | y) <;> simp [Matrix.sum_apply]

-- a double sum of `ρᵢρⱼ Kᵢ Mⱼ` factors
private theorem LinearSysDT.aux_sum_mul {k l : ℕ} (ρ : Fin r → ℝ) (K : Fin r → Mat ℝ n k)
    (M : Fin r → Mat ℝ k l) : -- --- CONCL ---
    ∑ i, ∑ j, (ρ i * ρ j) • (K i * M j) =
      (∑ i, ρ i • K i) * (∑ j, ρ j • M j) := by -- --- PROOF ---
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.lpvLmi_of_vertices (T : Mat ℝ n n) (N : Mat ℝ n ny) (C : Mat ℝ ny n)
    (F : Mat ℝ ny nd) (P : Mat ℝ n n) (Λ Y : Fin r → Mat ℝ n ny) (A : Fin r → Mat ℝ n n)
    (D : Fin r → Mat ℝ n nd) (α β : ℝ) (ρ : Fin r → ℝ) (hρ0 : ∀ i, 0 ≤ ρ i)
    (hρ1 : ∑ i, ρ i = 1) (hPT : Pᵀ = P) (hY : ∀ i, P * Λ i = Y i) : -- --- CONCL ---
    let Dg : Matrix (Fin n ⊕ (Fin nd ⊕ Fin nd)) (Fin n ⊕ (Fin nd ⊕ Fin nd)) ℝ :=
      fromBlocks (α • P) 0 0 (fromBlocks (((1 - α) * β) • 1) 0 0 (((1 - α) * (1 - β)) • 1))
    let R : Fin r → Fin r → Matrix (Fin n) (Fin n ⊕ (Fin nd ⊕ Fin nd)) ℝ := fun i j =>
      fromCols (P * T * A j - Y i * C * T * A j) (fromCols (P * T * D j - Y i * C * T * D j)
        (P * N * F - Y i * C * N * F + Y i * F))
    let Ψ : Fin r → Fin r → Matrix ((Fin n ⊕ (Fin nd ⊕ Fin nd)) ⊕ Fin n)
      ((Fin n ⊕ (Fin nd ⊕ Fin nd)) ⊕ Fin n) ℝ := fun i j => fromBlocks Dg (R i j)ᵀ (R i j) P
    let Λθ := ∑ i, ρ i • Λ i
    let Aθ := ∑ j, ρ j • A j
    let Dθ := ∑ j, ρ j • D j
    let Rθ := fromCols (P * (1 - Λθ * C) * T * Aθ) (fromCols (P * (1 - Λθ * C) * T * Dθ)
      (P * (N * F - Λθ * C * N * F + Λθ * F)))
    (∀ i, (Ψ i i).PosDef) →
      (∀ i j, i ≠ j → ((2 / ((r : ℝ) - 1)) • Ψ i i + Ψ i j + Ψ j i).PosDef) →
      (fromBlocks Dg Rθᵀ Rθ P).PosDef := by -- --- PROOF ---
  intro Dg R Ψ Λθ Aθ Dθ Rθ hd ho
  have hconst : ∀ {a b : Type} (M : Matrix a b ℝ), ∑ i, ∑ j, (ρ i * ρ j) • M = M := fun M => by
    simp only [← Finset.sum_smul, ← Finset.mul_sum, ← Finset.sum_mul, hρ1, one_mul, one_smul]
  have hsingle : ∀ {a b : Type} (M : Fin r → Matrix a b ℝ),
      ∑ i, ∑ j, (ρ i * ρ j) • M i = ∑ i, ρ i • M i := fun M => by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← smul_smul, ← Finset.smul_sum, ← Finset.sum_smul, hρ1, one_smul]
  -- `I - Λ(θ)C = Σᵢ ρᵢ (I - ΛᵢC)` and `Yᵢ = PΛᵢ`
  have hK : ∑ i, ρ i • (P * (1 - Λ i * C)) = P * (1 - Λθ * C) := by
    simp only [← Matrix.mul_smul, ← Matrix.mul_sum, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hρ1, one_smul, Λθ, Matrix.sum_mul, Matrix.smul_mul]
  have hT : ∀ {k : ℕ} (M : Fin r → Mat ℝ n k), ∑ j, ρ j • (T * M j) = T * ∑ j, ρ j • M j :=
    fun M => by simp only [Matrix.mul_sum, Matrix.mul_smul]
  -- the first two blocks, `(P - YᵢC) T Mⱼ = P(I - ΛᵢC) T Mⱼ`
  have hblk : ∀ {k : ℕ} (M : Fin r → Mat ℝ n k),
      ∑ i, ∑ j, (ρ i * ρ j) • (P * T * M j - Y i * C * T * M j) =
        P * (1 - Λθ * C) * T * ∑ j, ρ j • M j := fun M => by
    have h1 : ∀ i j, P * T * M j - Y i * C * T * M j = (P * (1 - Λ i * C)) * (T * M j) :=
      fun i j => by
        rw [← hY]; simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]
    simp only [h1]
    rw [LinearSysDT.aux_sum_mul ρ, hK, hT]
    simp only [Matrix.mul_assoc]
  -- the third block, affine in `Λᵢ`
  have hblk3 : ∑ i, ∑ j, (ρ i * ρ j) • (P * N * F - Y i * C * N * F + Y i * F) =
      P * (N * F - Λθ * C * N * F + Λθ * F) := by
    rw [hsingle]
    have h3 : ∀ i, P * N * F - Y i * C * N * F + Y i * F =
        P * (N * F - Λ i * (C * N * F) + Λ i * F) := fun i => by
      rw [← hY]; simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => by rw [h3 i]]
    simp only [← Matrix.mul_smul, ← Matrix.mul_sum, smul_add, smul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul, hρ1, one_smul,
      Λθ, Matrix.mul_assoc]
    simp only [Matrix.mul_smul, Matrix.sum_mul, Matrix.smul_mul]
  have hR : ∑ i, ∑ j, (ρ i * ρ j) • R i j = Rθ := by
    simp only [R, LinearSysDT.aux_sum_fromCols]
    rw [hblk A, hblk D, hblk3]
  -- the scheduled matrix is the weighted double sum of the vertex matrices
  have hsum : fromBlocks Dg Rθᵀ Rθ P = ∑ i, ∑ j, (ρ i * ρ j) • Ψ i j := by
    simp only [Ψ, LinearSysDT.aux_sum_fromBlocks, hconst, hR, ← transpose_smul,
      ← transpose_sum]
  rw [hsum]
  refine doubleSum_posDef Ψ ρ hρ0 hρ1 (fun i j => ?_) hd ho
  -- each vertex matrix is symmetric
  have hDg : Dgᵀ = Dg := by
    simp only [Dg, fromBlocks_transpose, transpose_smul, hPT, transpose_zero, transpose_one]
  simp only [Ψ, fromBlocks_transpose, transpose_transpose, hDg, hPT]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
