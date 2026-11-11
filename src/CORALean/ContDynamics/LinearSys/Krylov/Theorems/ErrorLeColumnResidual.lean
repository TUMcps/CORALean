module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeResidual
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpNegSmulMulVecLe
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# The Krylov error of real matrices from the column residuals of the Krylov identity

[1, Thm. 3] for real `A`, with the residual of the Krylov identity (2.2) given column by column.
`Krylov.error_le_residual` over `ℝ`, which is what the float Arnoldi iteration works in. The
residual `Δ = A V - V T - τ w e_m*` of the computed basis `V` and Hessenberg matrix `T` is given
by the Euclidean norms `ε_j` of its columns, the quantity a rounded-up evaluation of
`A v_j - Σ_i h_{ij} v_i` yields entry by entry; then `‖Δ x‖₂ ≤ (Σ_j ε_j)‖x‖₂` over `ℂ` too. The
real quadratic forms `x*Ax ≤ μ x*x` carry over to the complex Rayleigh quotients, `Re(z*Az) =
x*Ax + y*Ay`, and the exponentials of the complexified matrices are the complexified exponentials.

## Inputs
* `A` – matrix
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `w` – next vector
* `Δ` – residual of the Krylov identity
* `ε` – bounds on the Euclidean norms of the residual's columns
* `c` – start vector
* `ν` – scale of the first basis vector
* `ρ` – bound on how far `ν V e₁` is from the start vector
* `μ` – upper bound on the quadratic forms
* `t` – time

## Hypotheses
* `hK` – Krylov identity holds up to the residual
* `hΔ` – residual columns bounded
* `hc` – first basis vector scaled close to the start vector
* `hH` – Hessenberg matrix upper Hessenberg
* `hA` – quadratic form of the matrix at most the growth rate
* `hT` – quadratic form of the Hessenberg matrix at most the growth rate
* `ht` – time nonnegative

## Conclusion
* the Krylov error is at most the product bound with the growth factor, plus the residual's share

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A real vector as a complex one. -/
private def aux_cast {k : ℕ} (x : Fin k → ℝ) : Fin k → ℂ := fun i => (x i : ℂ)

/-- A real matrix as a complex one. -/
private abbrev aux_c {a b : ℕ} (M : Mat ℝ a b) : Mat ℂ a b := M.map ((↑) : ℝ → ℂ)

private theorem aux_norm_cast {k : ℕ} (x : Fin k → ℝ) :
    ‖(WithLp.toLp 2 (aux_cast x) : EuclideanSpace ℂ (Fin k))‖ = ‖x‖₂ := by
  rw [EuclideanSpace.norm_eq, norm₂]
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => by
    simp [aux_cast, Complex.norm_real, sq_abs])

private theorem aux_exp_map {k : ℕ} (M : Mat ℝ k k) :
    aux_c (exp M) = exp (aux_c M) :=
  map_exp (Complex.ofRealHom.mapMatrix (m := Fin k))
    (continuous_id.matrix_map Complex.continuous_ofReal) M

private theorem aux_mulVec_cast {k l : ℕ} (M : Mat ℝ k l) (x : Fin l → ℝ) :
    aux_c M *ᵥ aux_cast x = aux_cast (M *ᵥ x) := by
  -- the product with a real matrix commutes with the embedding
  ext i
  simp [aux_cast, mulVec, dotProduct]

private theorem aux_rayleigh {k : ℕ} (M : Mat ℝ k k) (z : Fin k → ℂ) :
    (star z ⬝ᵥ (aux_c M *ᵥ z)).re =
      (fun i => (z i).re) ⬝ᵥ (M *ᵥ fun i => (z i).re) +
        (fun i => (z i).im) ⬝ᵥ (M *ᵥ fun i => (z i).im) := by
  -- a complex Rayleigh quotient splits into its real and imaginary parts
  simp [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, Finset.sum_add_distrib]

private theorem aux_rayleigh_one {k : ℕ} (z : Fin k → ℂ) :
    (star z ⬝ᵥ z).re = (fun i => (z i).re) ⬝ᵥ (fun i => (z i).re) +
      (fun i => (z i).im) ⬝ᵥ (fun i => (z i).im) := by
  simp [dotProduct, Complex.re_sum, Finset.sum_add_distrib]

/-- The columns bound the operator: `‖Δ z‖₂ ≤ (Σ_j ε_j)‖z‖₂`. -/
private theorem aux_columns {k : ℕ} (Δ : Mat ℝ n k) (ε : Fin k → ℝ)
    (hΔ : ∀ j, ‖fun i => Δ i j‖₂ ≤ ε j) (z : Fin k → ℂ) : -- --- CONCL ---
    ‖(WithLp.toLp 2 (aux_c Δ *ᵥ z) : EuclideanSpace ℂ (Fin n))‖ ≤
      (∑ j, ε j) * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin k))‖ := by -- --- PROOF ---
  have hsum : (WithLp.toLp 2 (aux_c Δ *ᵥ z) : EuclideanSpace ℂ (Fin n)) =
      ∑ j, z j • (WithLp.toLp 2 (aux_cast fun i => Δ i j) : EuclideanSpace ℂ (Fin n)) := by
    ext i
    simp [aux_cast, mulVec, dotProduct, mul_comm]
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, aux_norm_cast]
  exact (mul_le_mul (PiLp.norm_apply_le (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin k)) j) (hΔ j)
    (norm₂_nonneg _) (norm_nonneg (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin k)))).trans
    (le_of_eq (mul_comm _ _))


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `‖c - νVe₁‖₂ ≤ ρ`: `‖e^{tA}c - ν V e^{tT}e₁‖₂ ≤ e^{tμ}(|ν|(|τ|‖w‖₂|γ|t^{m+1}/(m+1)! +
(Σ_j ε_j)t) + ρ)`, `γ = ∏ T_{j+1,j}`. -/
theorem Krylov.error_le_column_residual (A : Mat ℝ n n) (V : Mat ℝ n (m + 1))
    (T : Mat ℝ (m + 1) (m + 1)) (τ : ℝ) (w : Vec ℝ n) (Δ : Mat ℝ n (m + 1))
    (ε : Fin (m + 1) → ℝ) (c : Vec ℝ n) (ν ρ μ : ℝ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1) + Δ)
    (hΔ : ∀ j, ‖fun i => Δ i j‖₂ ≤ ε j)
    (hc : ‖c - ν • (V *ᵥ Pi.single 0 1)‖₂ ≤ ρ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hA : ∀ x : Vec ℝ n, x ⬝ᵥ (A *ᵥ x) ≤ μ * (x ⬝ᵥ x))
    (hT : ∀ x : Vec ℝ (m + 1), x ⬝ᵥ (T *ᵥ x) ≤ μ * (x ⬝ᵥ x)) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    ‖exp (t • A) *ᵥ c - ν • (V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1))‖₂ ≤
      Real.exp (t * μ) * (|ν| * (|τ| * ‖w‖₂ *
        (|∏ j : Fin m, T j.succ j.castSucc| * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) +
          (∑ j, ε j) * t) + ρ) := by -- --- PROOF ---
  have hK' : aux_c A * aux_c V = aux_c V * aux_c T + (τ : ℂ) • vecMulVec (aux_cast w)
      (Pi.single (Fin.last m) 1) + aux_c Δ := by
    ext i j
    have h := congrArg (fun r : ℝ => (r : ℂ)) (congrFun (congrFun hK i) j)
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
      Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul] at h
    simp only [aux_c, aux_cast, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      vecMulVec_apply, Matrix.map_apply, smul_eq_mul]
    rw [h]
    by_cases hj : j = Fin.last m <;> simp [hj]
  -- the quadratic forms of the complexified matrices
  have hA' : ∀ z : Fin n → ℂ, (star z ⬝ᵥ (aux_c A *ᵥ z)).re ≤ μ * (star z ⬝ᵥ z).re := fun z => by
    rw [aux_rayleigh, aux_rayleigh_one, mul_add]
    exact add_le_add (hA _) (hA _)
  have hT' : ∀ z : Fin (m + 1) → ℂ, (star z ⬝ᵥ (aux_c T *ᵥ z)).re ≤ μ * (star z ⬝ᵥ z).re :=
    fun z => by
    rw [aux_rayleigh, aux_rayleigh_one, mul_add]
    exact add_le_add (hT _) (hT _)
  have hH' : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → aux_c T i k = 0 := fun i k hik => by
    simp [hH i k hik]
  have h := _root_.CORALean.Krylov.error_le_residual (aux_c A) (aux_c V) (aux_c T) (τ : ℂ)
    (aux_cast w)
    (aux_c Δ) (∑ j, ε j) μ hK' (aux_columns Δ ε hΔ) hH' hA' hT' ht
  -- back to the real objects: the exponentials, the unit vector and the norms
  have hsm : ∀ {k : ℕ} (M : Mat ℝ k k), t • aux_c M = aux_c (t • M) := fun M => by
    ext i j
    simp [aux_c, Matrix.smul_apply]
  have he1 : (Pi.single 0 1 : Fin (m + 1) → ℂ) = aux_cast (Pi.single 0 1) := by
    ext i
    by_cases hi : i = 0 <;> simp [aux_cast, hi]
  have hvec : exp (t • aux_c A) *ᵥ (aux_c V *ᵥ Pi.single 0 1) -
      aux_c V *ᵥ (exp (t • aux_c T) *ᵥ Pi.single 0 1) =
      aux_cast (exp (t • A) *ᵥ (V *ᵥ Pi.single 0 1) - V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1)) := by
    rw [hsm, hsm, ← aux_exp_map, ← aux_exp_map, he1, aux_mulVec_cast, aux_mulVec_cast,
      aux_mulVec_cast, aux_mulVec_cast]
    ext i
    simp [aux_cast]
  have hprod : ‖∏ j : Fin m, aux_c T j.succ j.castSucc‖ = |∏ j : Fin m, T j.succ j.castSucc| := by
    have : ∏ j : Fin m, aux_c T j.succ j.castSucc = ((∏ j : Fin m, T j.succ j.castSucc : ℝ) : ℂ) :=
      by simp [aux_c, Complex.ofReal_prod]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  simp only [hvec, aux_norm_cast, hprod, Complex.norm_real, Real.norm_eq_abs] at h
  -- the start vector: `e^{tA}c - νVe^{tT}e₁ = e^{tA}(c - νVe₁) + ν(e^{tA}Ve₁ - Ve^{tT}e₁)`
  have hsplit : exp (t • A) *ᵥ c - ν • (V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1)) =
      exp (t • A) *ᵥ (c - ν • (V *ᵥ Pi.single 0 1)) +
        ν • (exp (t • A) *ᵥ (V *ᵥ Pi.single 0 1) - V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    abel
  have hexp : ‖exp (t • A) *ᵥ (c - ν • (V *ᵥ Pi.single 0 1))‖₂ ≤
      Real.exp (t * μ) * ‖c - ν • (V *ᵥ Pi.single 0 1)‖₂ := by
    set r := c - ν • (V *ᵥ Pi.single 0 1) with hr
    have hn := _root_.CORALean.Krylov.norm_exp_neg_smul_mulVec_le (-(aux_c A)) (-μ)
      (fun z => by
        have := hA' z
        rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
        -- the growth of `e^{tA}` on the start vector's error
        linarith) (aux_cast r) ht
    rw [neg_neg, hsm, ← aux_exp_map, aux_mulVec_cast, aux_norm_cast,
      aux_norm_cast, show -(t * -μ) = t * μ by ring] at hn
    exact hn
  rw [hsplit]
  refine (norm₂_add_le _ _).trans ?_
  rw [norm₂_smul]
  have h3 := mul_le_mul_of_nonneg_left h (abs_nonneg ν)
  have h4 := mul_le_mul_of_nonneg_left hc (Real.exp_pos (t * μ)).le
  nlinarith [h3, h4, hexp]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
