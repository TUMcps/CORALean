module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContDynamics.Conform.Theorems.UnrollAffine
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# The matrix inequality of the P-radius gains, one output after another

[1, Alg. 2], step `j`: with the gains of the first `j - 1` outputs known and `κₛ = I - λₛ cₛᵀ`,
`Ĥ_{k/j} ẑ` is `(κ_{j-1} ⋯ κ₀)(A θ + F γ) + ∑ₛ ηₛ (κ_{j-1} ⋯ κₛ₊₁) φₛ λₛ`, `uₛ = φₛ λₛ`. If the
matrix inequality with the rows `((∏κ) Gᵢ)ᵀ P`, `((∏κ) F)ᵀ P` and `((∏_{r>s} κᵣ) uₛ)ᵀ P` holds at
every vertex `Gᵢ` of `[A]`, then `‖Ĥ_{k/j} ẑ‖²_P ≤ β ‖θ‖²_P + ‖F γ‖² + ∑ₛ φₛ² ηₛ²` for every `A`
in their hull: `quadForm_le_of_lmi` for `j` outputs, by the same Schur complement, the row of the
single output replaced by one row per output. The unknown gain `λ_{j-1} = P⁻¹ Y` enters through
`κ_{j-1}` and `u_{j-1}`; here the gains are all given, and the inequality is what makes them good.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: the matrix inequality of step `j` bounds the quadratic form of `Ĥ_{k/j} ẑ`. -/
theorem LinearSysDT.quadForm_le_of_lmi_chain (j : ℕ) (G : Fin q → Mat ℝ n n) (F : Mat ℝ n m)
    (κ : ℕ → Mat ℝ n n) (u : ℕ → Vec ℝ n) (φ : ℕ → ℝ) (β : ℝ) (P : Mat ℝ n n) (hP : P.PosDef)
    (hLMI : ∀ i,
      let Ξ : Matrix (Fin n ⊕ (Fin m ⊕ Fin j)) (Fin n) ℝ :=
        fromRows ((Conform.prodJac κ j j * G i)ᵀ * P)
          (fromRows ((Conform.prodJac κ j j * F)ᵀ * P)
            (Matrix.of fun s c => (Conform.prodJac κ j (j - s - 1) *ᵥ u s) ⬝ᵥ fun r => P r c))
      (fromBlocks (fromBlocks (β • P) 0 0
        (fromBlocks (Fᵀ * F) 0 0 (diagonal fun s : Fin j => φ s ^ 2))) Ξ Ξᵀ P).PosSemidef)
    (A : Mat ℝ n n) (hA : A ∈ convexHull ℝ (Set.range G)) (θ : Vec ℝ n) (γ : Vec ℝ m)
    (η : Fin j → ℝ) : -- --- STMT ---
    let e := Conform.prodJac κ j j *ᵥ (A *ᵥ θ + F *ᵥ γ)
      + ∑ s : Fin j, η s • (Conform.prodJac κ j (j - s - 1) *ᵥ u s)
    e ⬝ᵥ (P *ᵥ e) ≤ β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ)
      + ∑ s : Fin j, φ s ^ 2 * η s ^ 2 := by -- --- PROOF ---
  intro e
  set D : Matrix (Fin n ⊕ (Fin m ⊕ Fin j)) (Fin n ⊕ (Fin m ⊕ Fin j)) ℝ :=
    fromBlocks (β • P) 0 0 (fromBlocks (Fᵀ * F) 0 0 (diagonal fun s : Fin j => φ s ^ 2)) with hD
  set M : Mat ℝ n n := Conform.prodJac κ j j with hM
  let W : Fin j → Vec ℝ n := fun s => Conform.prodJac κ j (j - s - 1) *ᵥ u s
  let Ξ : Mat ℝ n n → Matrix (Fin n ⊕ (Fin m ⊕ Fin j)) (Fin n) ℝ := fun B =>
    fromRows ((M * B)ᵀ * P)
      (fromRows ((M * F)ᵀ * P) (Matrix.of fun s c => W s ⬝ᵥ fun r => P r c))
  let lmi : Mat ℝ n n → Matrix _ _ ℝ := fun B => fromBlocks D (Ξ B) (Ξ B)ᵀ P
  -- the matrix is affine in the vertex, so it stays semidefinite on the hull
  have haff : ∀ (A₁ A₂ : Mat ℝ n n) (a b : ℝ), a + b = 1 →
      lmi (a • A₁ + b • A₂) = a • lmi A₁ + b • lmi A₂ := by
    intro A₁ A₂ a b hab
    obtain rfl : b = 1 - a := by linarith
    ext (((i | i | i) | i)) (((j' | j' | j') | j')) <;>
      simp [lmi, Ξ, D, Matrix.mul_apply, Finset.mul_sum, add_mul, sub_mul,
        Finset.sum_sub_distrib]
  have hconv : Convex ℝ {B : Mat ℝ n n | (lmi B).PosSemidef} := by
    intro A₁ h₁ A₂ h₂ a b ha hb hab
    show (lmi (a • A₁ + b • A₂)).PosSemidef
    rw [haff A₁ A₂ a b hab]
    exact (h₁.smul ha).add (h₂.smul hb)
  have hAlmi : (lmi A).PosSemidef :=
    convexHull_min (Set.range_subset_iff.mpr fun i => hLMI i) hconv hA
  -- the Schur complement at `P`
  haveI : Invertible P := hP.isUnit.invertible
  have hT : (Ξ A)ᴴ = (Ξ A)ᵀ := conjTranspose_eq_transpose_of_trivial _
  have hS := (PosDef.fromBlocks₂₂ D (Ξ A) hP).mp (by rw [hT]; exact hAlmi)
  rw [hT] at hS
  have hPT : Pᵀ = P := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian.eq
  set v : (Fin n ⊕ (Fin m ⊕ Fin j)) → ℝ := Sum.elim θ (Sum.elim γ η) with hv
  have hu : (Ξ A)ᵀ *ᵥ v = P *ᵥ e := by
    simp only [Ξ, transpose_fromRows, v, fromCols_mulVec_sumElim, transpose_mul,
      transpose_transpose, hPT]
    have hsym : ∀ r c, P r c = P c r := fun r c => by
      simpa [transpose_apply] using (congrFun (congrFun hPT r) c).symm
    -- the input rows: `Pᵀ Wₛ` weighted by `ηₛ`
    have h3 : (of fun s c => W s ⬝ᵥ fun r => P r c)ᵀ *ᵥ η = P *ᵥ ∑ s, η s • W s := by
      ext c
      simp only [mulVec, dotProduct, transpose_apply, of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.mul_sum, hsym _ c]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [h3, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [e, mulVec_add, hM]
    abel
  -- the two halves of the quadratic form
  have hDv : v ⬝ᵥ (D *ᵥ v) =
      β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) + ∑ s : Fin j, φ s ^ 2 * η s ^ 2 := by
    have hF : γ ⬝ᵥ ((Fᵀ * F) *ᵥ γ) = (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) := by
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    have h1 : η ⬝ᵥ ((diagonal fun s : Fin j => φ s ^ 2) *ᵥ η) = ∑ s : Fin j, φ s ^ 2 * η s ^ 2 := by
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp only [hD, v, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec,
      add_zero, zero_add, sumElim_dotProduct_sumElim, smul_mulVec, dotProduct_smul, smul_eq_mul,
      hF, h1]
    ring
  have hXv : v ⬝ᵥ ((Ξ A * P⁻¹ * (Ξ A)ᵀ) *ᵥ v) = e ⬝ᵥ (P *ᵥ e) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hu,
      mulVec_mulVec, inv_mul_of_invertible, one_mulVec, dotProduct_comm]
  have hq := (posSemidef_iff_dotProduct_mulVec.mp hS).2 v
  rw [star_trivial, sub_mulVec, dotProduct_sub, hDv, hXv] at hq
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
