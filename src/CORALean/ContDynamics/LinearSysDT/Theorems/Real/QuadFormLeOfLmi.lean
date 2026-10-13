module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# The linear matrix inequality of the P-radius gain

[1, Eq. 9]: if `P ≻ 0`, `Y` and `β` satisfy the matrix inequality
`[βP 0 0 GᵢᵀP - Gᵢᵀc₁Yᵀ; ∗ FᵀF 0 FᵀP - Fᵀc₁Yᵀ; ∗ ∗ φ₁² Yᵀφ₁; ∗ ∗ ∗ P] ≽ 0` at every vertex `Gᵢ`
of the interval matrix `[A]`, then the gain `λ₁ = P⁻¹ Y` makes the quadratic form of
[1, Eq. 8] nonpositive at every `A` in the convex hull of the vertices:
`‖κ₁ A θ + κ₁ F γ + φ₁ λ₁ η‖²_P ≤ β ‖θ‖²_P + ‖F γ‖²₂ + φ₁² η²`, `κ₁ = I - λ₁ c₁ᵀ`, which is what
`Zonotope.pRadius_predict_strip_le` turns into the P-radius bound [1, Eq. 4].

Two steps, as in the paper. The matrix is affine in the vertex, so the set of `A` at which it is
semidefinite is convex and holds the hull. At one `A`, the Schur complement
(`Matrix.PosDef.fromBlocks₂₂`) gives `diag(βP, FᵀF, φ₁²) - Ξ P⁻¹ Ξᵀ ≽ 0`, and with `Y = P λ₁`,
`Ξᵀ (θ, γ, η) = P (κ₁ A θ + κ₁ F γ + φ₁ λ₁ η)`, so the quadratic form at `(θ, γ, η)` is Eq. 8.
That `[A]` is the hull of its vertices is `Interval.construct_subset_convexHull_vertices`. The
objective of Eq. 9, `max τ` with `(1 - β)P/(φ₁² + ψ) ≽ τ I`, is how the paper picks among the
feasible gains; every feasible one is sound.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.quadForm_le_of_lmi (G : Fin q → Mat ℝ n n) (F : Mat ℝ n m) (c Y : Vec ℝ n)
    (φ β : ℝ) (P : Mat ℝ n n) (hP : P.PosDef)
    (hLMI : ∀ i,
      let Ξ : Matrix (Fin n ⊕ (Fin m ⊕ Fin 1)) (Fin n) ℝ :=
        fromRows ((G i)ᵀ * P - (G i)ᵀ * vecMulVec c Y)
          (fromRows (Fᵀ * P - Fᵀ * vecMulVec c Y) (Matrix.of fun _ j => Y j * φ))
      (fromBlocks (fromBlocks (β • P) 0 0 (fromBlocks (Fᵀ * F) 0 0 (Matrix.of fun _ _ => φ ^ 2)))
        Ξ Ξᵀ P).PosSemidef)
    (A : Mat ℝ n n) (hA : A ∈ convexHull ℝ (Set.range G)) (θ : Vec ℝ n) (γ : Vec ℝ m) (η : ℝ) :
    let l := P⁻¹ *ᵥ Y
    let κ : Mat ℝ n n := 1 - vecMulVec l c
    let e := κ *ᵥ (A *ᵥ θ) + κ *ᵥ (F *ᵥ γ) + (φ * η) • l
    e ⬝ᵥ (P *ᵥ e) ≤
      β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) + φ ^ 2 * η ^ 2 := by -- --- PROOF ---
  intro l κ e
  set D : Matrix (Fin n ⊕ (Fin m ⊕ Fin 1)) (Fin n ⊕ (Fin m ⊕ Fin 1)) ℝ :=
    fromBlocks (β • P) 0 0 (fromBlocks (Fᵀ * F) 0 0 (Matrix.of fun _ _ => φ ^ 2)) with hD
  let Ξ : Mat ℝ n n → Matrix (Fin n ⊕ (Fin m ⊕ Fin 1)) (Fin n) ℝ := fun B =>
    fromRows (Bᵀ * P - Bᵀ * vecMulVec c Y)
      (fromRows (Fᵀ * P - Fᵀ * vecMulVec c Y) (Matrix.of fun _ j => Y j * φ))
  let lmi : Mat ℝ n n → Matrix _ _ ℝ := fun B => fromBlocks D (Ξ B) (Ξ B)ᵀ P
  -- the matrix is affine in the vertex, so it stays semidefinite on the hull
  have haff : ∀ (A₁ A₂ : Mat ℝ n n) (a b : ℝ), a + b = 1 →
      lmi (a • A₁ + b • A₂) = a • lmi A₁ + b • lmi A₂ := by
    intro A₁ A₂ a b hab
    obtain rfl : b = 1 - a := by linarith
    ext (((i | i | i) | i)) (((j | j | j) | j)) <;>
      simp [lmi, Ξ, D, Matrix.mul_apply, vecMulVec, Finset.mul_sum, add_mul, sub_mul, mul_sub,
        Finset.sum_sub_distrib] <;> ring
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
  -- `P λ₁ = Y`, and so `P κ₁ w = P w - (c₁ᵀ w) Y`
  have hPl : P *ᵥ l = Y := by simp [l, mulVec_mulVec]
  have hPκ : ∀ w, P *ᵥ (κ *ᵥ w) = P *ᵥ w - (c ⬝ᵥ w) • Y := fun w => by
    simp only [κ, sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      mulVec_sub, mulVec_smul, hPl]
  -- `Ξᵀ (θ, γ, η) = P e`
  set v : (Fin n ⊕ (Fin m ⊕ Fin 1)) → ℝ := Sum.elim θ (Sum.elim γ fun _ => η)
  have hu : (Ξ A)ᵀ *ᵥ v = P *ᵥ e := by
    simp only [Ξ, transpose_fromRows, v, fromCols_mulVec_sumElim, transpose_sub, transpose_mul,
      transpose_transpose, transpose_vecMulVec, hPT, sub_mulVec, ← mulVec_mulVec,
      vecMulVec_mulVec, op_smul_eq_smul, e, mulVec_add, hPκ, mulVec_smul, hPl]
    ext i
    simp [Matrix.mulVec, dotProduct]
    ring
  -- the two halves of the quadratic form
  have hDv : v ⬝ᵥ (D *ᵥ v) =
      β * (θ ⬝ᵥ (P *ᵥ θ)) + (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) + φ ^ 2 * η ^ 2 := by
    have hF : γ ⬝ᵥ ((Fᵀ * F) *ᵥ γ) = (F *ᵥ γ) ⬝ᵥ (F *ᵥ γ) := by
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    have h1 : (fun _ : Fin 1 => η) ⬝ᵥ
        ((Matrix.of fun _ _ => φ ^ 2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun _ => η) =
        φ ^ 2 * η ^ 2 := by
      simp [dotProduct, Matrix.mulVec]; ring
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
