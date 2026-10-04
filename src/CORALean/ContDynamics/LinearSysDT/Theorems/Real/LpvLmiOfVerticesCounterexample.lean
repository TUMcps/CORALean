import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real

/-!
# The vertex conditions of the LPV estimator as printed

[1, Cor. 2] concludes Eq. 19 of [1, Thm. 2] at the scheduled matrices from `Ψᵢᵢ ≻ 0` (its
Eq. 29a) and `2/(h-1) Ψᵢᵢ + Ψᵢⱼ + Ψⱼᵢ ≽ 0` for `i < j` (its Eq. 29b), `Ψᵢⱼ` its Eq. 30. With
`h = 2` vertices, `n_x = n_y = n_d = 1`, `T = N = C = 1`, `F = 0`, `D_j = 0`, `A₁ = 0`, `A₂ = 1`,
`P = 2`, `Y₁ = -2`, `Y₂ = 3/2` (`Λᵢ = P⁻¹Yᵢ = -1, 3/4`), `α = 1/4`, `β = 1/2`, the only coupling in
`Ψᵢⱼ` is `(2 - Yᵢ)Aⱼ`, between the first and the last block: `0` in `Ψ₁₁`, `1/2` in `Ψ₂₂`, so both
are positive definite, and `4` in `2Ψ₁₁ + Ψ₁₂ + Ψ₂₁`, which is singular and positive semidefinite.
At `ρ = (1/2, 1/2)` the coupling of Eq. 19 is `P(1 - Λ(θ)C)TA(θ) = 9/8`, and its form at
`(1, 0, 0, -9/16)` is `-17/128`. The condition for `(j, i) = (2, 1)`, which the corollary omits,
fails; with it, strict, the corollary holds (`lpvLmi_of_vertices`).

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the form of a `4 × 4` block matrix, entry by entry
theorem LinearSysDT.aux_form4 (M : Matrix ((Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ⊕ Fin 1)
    ((Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ⊕ Fin 1) ℝ) (x : (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ⊕ Fin 1 → ℝ) :
    star x ⬝ᵥ (M *ᵥ x) = ∑ a, ∑ b, x a * M a b * x b := by
  simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

-- a nonzero vector has a nonzero coordinate
theorem LinearSysDT.aux_coord4 (x : (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ⊕ Fin 1 → ℝ) (hx : x ≠ 0) :
    x (Sum.inl (Sum.inl 0)) ≠ 0 ∨ x (Sum.inl (Sum.inr (Sum.inl 0))) ≠ 0 ∨
      x (Sum.inl (Sum.inr (Sum.inr 0))) ≠ 0 ∨ x (Sum.inr 0) ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hx (funext fun k => by
    rcases k with (k | k | k) | k <;> fin_cases k <;> simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2])


-- =======================================  MAIN THEOREM  ======================================= --

-- simp evaluates the forms of four concrete `4 × 4` block matrices entry by entry
set_option maxHeartbeats 400000 in
theorem LinearSysDT.lpvLmi_of_vertices_counterexample :
    let T : Mat ℝ 1 1 := 1
    let N : Mat ℝ 1 1 := 1
    let C : Mat ℝ 1 1 := 1
    let F : Mat ℝ 1 1 := 0
    let P : Mat ℝ 1 1 := fun _ _ => 2
    let Λ : Fin 2 → Mat ℝ 1 1 := ![fun _ _ => -1, fun _ _ => 3 / 4]
    let Y : Fin 2 → Mat ℝ 1 1 := ![fun _ _ => -2, fun _ _ => 3 / 2]
    let A : Fin 2 → Mat ℝ 1 1 := ![0, 1]
    let D : Fin 2 → Mat ℝ 1 1 := fun _ => 0
    let α : ℝ := 1 / 4
    let β : ℝ := 1 / 2
    let ρ : Fin 2 → ℝ := fun _ => 1 / 2
    -- the vertex matrices `Ψᵢⱼ` of Eq. 30, and Eq. 19 at the scheduled matrices
    let Dg : Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ℝ :=
      fromBlocks (α • P) 0 0 (fromBlocks (((1 - α) * β) • 1) 0 0 (((1 - α) * (1 - β)) • 1))
    let R : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ℝ := fun i j =>
      fromCols (P * T * A j - Y i * C * T * A j) (fromCols (P * T * D j - Y i * C * T * D j)
        (P * N * F - Y i * C * N * F + Y i * F))
    let Ψ := fun i j => fromBlocks Dg (R i j)ᵀ (R i j) P
    let Λθ := ∑ i, ρ i • Λ i
    let Aθ := ∑ j, ρ j • A j
    let Dθ := ∑ j, ρ j • D j
    let Rθ := fromCols (P * (1 - Λθ * C) * T * Aθ) (fromCols (P * (1 - Λθ * C) * T * Dθ)
      (P * (N * F - Λθ * C * N * F + Λθ * F)))
    (∀ i, P * Λ i = Y i) ∧ (∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1 ∧ (∀ i, (Ψ i i).PosDef) ∧
      (∀ i j, i < j → ((2 / ((2 : ℝ) - 1)) • Ψ i i + Ψ i j + Ψ j i).PosSemidef) ∧
      ¬ (fromBlocks Dg Rθᵀ Rθ P).PosDef := by -- --- PROOF ---
  intro T N C F P Λ Y A D α β ρ Dg R Ψ Λθ Aθ Dθ Rθ
  refine ⟨fun i => ?_, fun _ => by norm_num [ρ], by simp [ρ], fun i => ?_, fun i j hij => ?_, ?_⟩
  · -- `PΛᵢ = Yᵢ`
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [P, Λ, Y, Matrix.mul_apply]
  · -- `Ψ₁₁`, `Ψ₂₂`: couplings `0` and `1/2`
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext ((a | a | a) | a) ((b | b | b) | b) <;> fin_cases a <;> fin_cases b <;>
        simp [Ψ, Dg, R, fromBlocks, fromCols, T, N, C, F, P, D, A, Y, α, β]
    -- the form, entry by entry, against a nonzero coordinate
    have hc := LinearSysDT.aux_coord4 x hx
    rw [LinearSysDT.aux_form4]
    fin_cases i <;>
      simp [Fintype.sum_sum_type, Ψ, Dg, R, T, N, C, F, P, D, A, Y, α, β, fromBlocks,
        fromCols] <;>
      rcases hc with h | h | h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x (Sum.inl (Sum.inl 0)) + x (Sum.inr 0)),
        sq_nonneg (x (Sum.inl (Sum.inl 0))), sq_nonneg (x (Sum.inl (Sum.inr (Sum.inl 0)))),
        sq_nonneg (x (Sum.inl (Sum.inr (Sum.inr 0)))), sq_nonneg (x (Sum.inr 0))]
  · -- `2Ψ₁₁ + Ψ₁₂ + Ψ₂₁`: coupling `4`, form `2(x₁ + 2x₄)² + 3/2 (x₂² + x₃²)`
    fin_cases i <;> fin_cases j <;> simp at hij
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
    · ext ((a | a | a) | a) ((b | b | b) | b) <;> fin_cases a <;> fin_cases b <;>
        simp [Ψ, Dg, R, fromBlocks, fromCols, T, N, C, F, P, D, A, Y, α, β]
    rw [LinearSysDT.aux_form4]
    simp [Fintype.sum_sum_type, Ψ, Dg, R, T, N, C, F, P, D, A, Y, α, β, fromBlocks, fromCols]
    nlinarith [sq_nonneg (x (Sum.inl (Sum.inl 0)) + 2 * x (Sum.inr 0)),
      sq_nonneg (x (Sum.inl (Sum.inr (Sum.inl 0)))), sq_nonneg (x (Sum.inl (Sum.inr (Sum.inr 0))))]
  · -- Eq. 19 at `ρ = (1/2, 1/2)`: the form at `(1, 0, 0, -9/16)` is negative
    intro h
    have := (posDef_iff_dotProduct_mulVec.mp h).2
      (x := Sum.elim (Sum.elim (fun _ => 1) 0) (fun _ => -9 / 16)) (by
        intro hx; have := congrFun hx (Sum.inl (Sum.inl 0)); simp at this)
    rw [LinearSysDT.aux_form4] at this
    simp [Fintype.sum_sum_type, Dg, Rθ, Λθ, Aθ, Dθ, ρ, Λ, A, D, P, T, C, N, F, α, β, fromBlocks,
      fromCols, Matrix.mul_apply, Fin.sum_univ_two] at this
    norm_num at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
