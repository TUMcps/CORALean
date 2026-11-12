module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.QuadExpLeWeighted
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.RestartedErrorLeGrowth
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

/-!
# The error of restarted Krylov steps, with the exact steps measured in a Lyapunov weight

[1, Sec. 7]'s accumulation of local errors for `E_j = e^{Δt_j A}` with a weight `P`, `x*PAx ≤ μ
x*Px`, `a x*x ≤ x*Px ≤ b x*x`. In the 2-norm `e^{tA}` of a non-normal `A` is not nonexpansive
though it decays; in the gauge `ν(x) = √(x*Px)` it grows by `e^{μΔt_j}` per step
(`Krylov.quad_exp_le_weighted`), the gauge is subadditive (Cauchy–Schwarz for `P`) and `√a ‖x‖₂ ≤
ν(x) ≤ √b ‖x‖₂`. So `Krylov.restarted_error_le_growth` gives the 2-norm error at most `β_N/√a`,
with the local 2-norm errors `ε'_j` entering as `ε_j = √b ε'_j`: the factor `√(b/a)` is paid once,
not per step.

## Inputs
* `A` – matrix
* `P` – symmetric weight
* `μ` – growth rate in the weight
* `a` – lower bound of the weight's quadratic form
* `b` – upper bound of the weight's quadratic form
* `N` – number of substeps
* `Δt` – substep lengths
* `v` – exact iterates
* `w` – approximate iterates
* `S` – approximate step maps
* `ε` – local 2-norm errors
* `β` – bound of the accumulated error in the weight

## Hypotheses
* `hS` – weight symmetric
* `hPA` – `x*PAx ≤ μ x*Px`
* `ha` – `a x*x ≤ x*Px`
* `hb` – `x*Px ≤ b x*x`
* `ha0` – `a` positive
* `hΔt` – substep lengths nonnegative
* `hv` – exact iterates follow the exact steps
* `hw` – approximate iterates follow the approximate steps
* `h0` – both start at the same vector
* `hloc` – local errors within `ε_j`
* `hβ0` – bound nonnegative at the start
* `hβ` – bound follows the recursion `e^{μΔt_j} β_j + √b ε_j ≤ β_{j+1}`

## Conclusion
* the 2-norm error is at most `β_N/√a`

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Cauchy–Schwarz for a symmetric positive semidefinite weight. -/
private theorem aux_cs_weighted (P : Mat ℝ n n) (hS : Pᵀ = P)
    (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (P *ᵥ x)) (u v : Vec ℝ n) : -- --- CONCL ---
    (u ⬝ᵥ (P *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (P *ᵥ u)) * (v ⬝ᵥ (P *ᵥ v)) := by -- --- PROOF ---
  have hsym : ∀ u v : Vec ℝ n, u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := fun u v => by
    rw [dotProduct_comm, ← vecMul_transpose, hS, ← dotProduct_mulVec]
  have h := discrim_le_zero (a := v ⬝ᵥ (P *ᵥ v)) (b := 2 * (u ⬝ᵥ (P *ᵥ v))) (c := u ⬝ᵥ (P *ᵥ u))
    fun s => by
      have := hpsd (u + s • v)
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
      rw [hsym v u] at this
      nlinarith [this]
  unfold discrim at h
  nlinarith [h]

/-- The weighted gauge is subadditive. -/
private theorem aux_gauge_add_le (P : Mat ℝ n n) (hS : Pᵀ = P)
    (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (P *ᵥ x)) (x y : Vec ℝ n) : -- --- CONCL ---
    Real.sqrt ((x + y) ⬝ᵥ (P *ᵥ (x + y))) ≤
      Real.sqrt (x ⬝ᵥ (P *ᵥ x)) + Real.sqrt (y ⬝ᵥ (P *ᵥ y)) := by -- --- PROOF ---
  have hsym : ∀ u v : Vec ℝ n, u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := fun u v => by
    rw [dotProduct_comm, ← vecMul_transpose, hS, ← dotProduct_mulVec]
  have hcs := aux_cs_weighted P hS hpsd x y
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have hx := Real.sq_sqrt (hpsd x)
  have hy := Real.sq_sqrt (hpsd y)
  have hxy : x ⬝ᵥ (P *ᵥ y) ≤ Real.sqrt (x ⬝ᵥ (P *ᵥ x)) * Real.sqrt (y ⬝ᵥ (P *ᵥ y)) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, hx, hy]; exact hcs
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [hsym y x]
  nlinarith [hxy, hx, hy]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `x*PAx ≤ μ x*Px`, `a x*x ≤ x*Px ≤ b x*x`, exact steps `v^{[j+1]} = e^{Δt_j A} v^{[j]}`,
2-norm local errors `‖e^{Δt_j A} w^{[j]} - w^{[j+1]}‖₂ ≤ ε_j` and `e^{μΔt_j} β_j + √b ε_j ≤
β_{j+1}`: `‖v^{[N]} - w^{[N]}‖₂ ≤ β_N/√a`. -/
theorem Krylov.restarted_error_le_weighted (A P : Mat ℝ n n) (μ a b : ℝ) (hS : Pᵀ = P)
    (hPA : ∀ x, x ⬝ᵥ (P *ᵥ (A *ᵥ x)) ≤ μ * (x ⬝ᵥ (P *ᵥ x)))
    (ha : ∀ x, a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) (hb : ∀ x, x ⬝ᵥ (P *ᵥ x) ≤ b * (x ⬝ᵥ x))
    (ha0 : 0 < a) (N : ℕ) (Δt : ℕ → ℝ) (hΔt : ∀ j < N, 0 ≤ Δt j) (v w : ℕ → Vec ℝ n)
    (S : ℕ → Vec ℝ n → Vec ℝ n) (ε β : ℕ → ℝ)
    (hv : ∀ j < N, v (j + 1) = exp (Δt j • A) *ᵥ v j) (hw : ∀ j < N, w (j + 1) = S j (w j))
    (h0 : v 0 = w 0) (hloc : ∀ j < N, ‖exp (Δt j • A) *ᵥ w j - S j (w j)‖₂ ≤ ε j)
    (hβ0 : 0 ≤ β 0)
    (hβ : ∀ j < N, Real.exp (μ * Δt j) * β j + Real.sqrt b * ε j ≤ β (j + 1)) : -- --- CONCL ---
    ‖v N - w N‖₂ ≤ β N / Real.sqrt a := by -- --- PROOF ---
  have hpsd : ∀ x, 0 ≤ x ⬝ᵥ (P *ᵥ x) := fun x => by
    have := ha x
    rw [dotProduct_self] at this
    exact le_trans (by positivity) this
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  -- the gauge `ν(x) = √(x*Px)` is squeezed between the 2-norm and its weight bounds
  set ν : Vec ℝ n → ℝ := fun x => Real.sqrt (x ⬝ᵥ (P *ᵥ x)) with hν
  have hlo : ∀ x, Real.sqrt a * ‖x‖₂ ≤ ν x := fun x => by
    rw [← Real.sqrt_sq (norm₂_nonneg x), ← Real.sqrt_mul ha0.le]
    refine Real.sqrt_le_sqrt ?_
    have := ha x
    rw [dotProduct_self] at this
    linarith
  -- and from above
  have hhi : ∀ x, ν x ≤ Real.sqrt b * ‖x‖₂ := fun x => by
    rw [← Real.sqrt_sq (norm₂_nonneg x), ← Real.sqrt_mul' _ (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have := hb x
    rw [dotProduct_self] at this
    linarith
  -- the exact step grows the gauge by `e^{μΔt_j}`
  have hE : ∀ j < N, ∀ x, ν ((Matrix.mulVecLin (exp (Δt j • A))).toAddMonoidHom x) ≤
      Real.exp (μ * Δt j) * ν x := fun j hj x => by
    simp only [hν, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
    have h := Krylov.quad_exp_le_weighted A P μ hS hPA x (hΔt j hj)
    calc _ ≤ Real.sqrt (Real.exp (2 * μ * Δt j) * (x ⬝ᵥ (P *ᵥ x))) := Real.sqrt_le_sqrt h
      _ = _ := by
        rw [Real.sqrt_mul (Real.exp_pos _).le, show 2 * μ * Δt j = μ * Δt j + μ * Δt j by ring,
          Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hmain := Krylov.restarted_error_le_growth ν (fun x y => aux_gauge_add_le P hS hpsd x y)
    (by simp [hν]) (fun j => (Matrix.mulVecLin (exp (Δt j • A))).toAddMonoidHom) S v w
    (fun j => Real.exp (μ * Δt j)) (fun j => Real.sqrt b * ε j) β N
    (fun j _ => (Real.exp_pos _).le) hE (fun j hj => by simpa using hv j hj) hw h0
    (fun j hj => by
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
      exact (hhi _).trans (mul_le_mul_of_nonneg_left (hloc j hj) (Real.sqrt_nonneg _)))
    hβ0 hβ
  have := (hlo (v N - w N)).trans hmain
  rw [le_div_iff₀ hsa, mul_comm]
  exact this


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
