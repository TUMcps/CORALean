module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.LogDetHalderEq
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLogDetHasDerivAt

@[expose] public section

/-!
# The derivative of the log-determinant of the outer ellipsoid

[1, Eq. 17]: `∂/∂β log det Q(β) = −(1/(β(1+β))) trace((I + βR)⁻¹ (I − β²R))`, `R = Q₁⁻¹ Q₂`.
The printed derivation applies Jacobi's formula to `Q(β)` with [1, Eq. 15] and [1, Eq. 16].
Here `R = S Λ T` and the trace of `S diag((1 − β²λᵢ)/(1+βλᵢ)) T` is the stationarity sum,
so the derivative is that of `log det Q₁ + ∑ᵢ log((1 + 1/β) + (1 + β)λᵢ)`.

## Inputs
* `Q₁` – first shape matrix
* `Q₂` – second shape matrix
* `β` – weight of the shape sum

## Hypotheses
* `h₁` – `Q₁` positive definite
* `h₂` – `Q₂` positive definite
* `hβ` – `0 < β`

## Conclusion
* the derivative of `log det Q(β)` is a trace in `Q₁⁻¹ Q₂`

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 17]: the derivative of `log det Q(β)` as a trace in `R = Q₁⁻¹ Q₂`. -/
theorem Ellipsoid.halder_deriv_log_det {Q₁ Q₂ : Matrix n n ℝ} (h₁ : Q₁.PosDef)
    (h₂ : Q₂.PosDef) {β : ℝ} (hβ : 0 < β) : -- --- CONCL ---
    HasDerivAt (fun b : ℝ => Real.log (((1 + 1 / b) • Q₁ + (1 + b) • Q₂).det))
      (-(1 / (β * (1 + β))) *
        ((1 + β • (Q₁⁻¹ * Q₂))⁻¹ * (1 - β ^ 2 • (Q₁⁻¹ * Q₂))).trace) β := by -- --- PROOF ---
  obtain ⟨S, T, lam, hST, hTS, hR, hpos, hlog⟩ := Ellipsoid.log_det_halder_eq h₁ h₂
  have hden : ∀ i, 1 + β * lam i ≠ 0 := fun i => by have := hpos i; positivity
  -- `I + βR` and `I − β²R` are `S` times a diagonal matrix times `T`
  have h1 : (1 : Matrix n n ℝ) + β • (S * diagonal lam * T)
      = S * diagonal (fun i => 1 + β * lam i) * T := by
    have : (diagonal (fun i => 1 + β * lam i) : Matrix n n ℝ) = 1 + β • diagonal lam := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, mul_add, add_mul, mul_one, hST, mul_smul_comm, smul_mul_assoc]
  have h2 : (1 : Matrix n n ℝ) - β ^ 2 • (S * diagonal lam * T)
      = S * diagonal (fun i => 1 - β ^ 2 * lam i) * T := by
    have : (diagonal (fun i => 1 - β ^ 2 * lam i) : Matrix n n ℝ) = 1 - β ^ 2 • diagonal lam := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, mul_sub, sub_mul, mul_one, hST, mul_smul_comm, smul_mul_assoc]
  -- and the inverse of the first is `S` times the reciprocal diagonal times `T`
  have hinv : (S * diagonal (fun i => 1 + β * lam i) * T)⁻¹
      = S * diagonal (fun i => (1 + β * lam i)⁻¹) * T := by
    refine inv_eq_right_inv ?_
    calc S * diagonal (fun i => 1 + β * lam i) * T
          * (S * diagonal (fun i => (1 + β * lam i)⁻¹) * T)
        = S * (diagonal (fun i => 1 + β * lam i) * (T * S)
          * diagonal (fun i => (1 + β * lam i)⁻¹)) * T := by simp only [mul_assoc]
      _ = 1 := by
        rw [hTS, mul_one, diagonal_mul_diagonal]
        have : (fun i => (1 + β * lam i) * (1 + β * lam i)⁻¹) = fun _ => (1:ℝ) := by
          funext i; exact mul_inv_cancel₀ (hden i)
        rw [this, diagonal_one, mul_one, hST]
  -- so the trace is the stationarity sum
  have htr : ((1 + β • (Q₁⁻¹ * Q₂))⁻¹ * (1 - β ^ 2 • (Q₁⁻¹ * Q₂))).trace
      = Ellipsoid.halderStationarity lam β := by
    rw [hR, h1, hinv, h2]
    calc (S * diagonal (fun i => (1 + β * lam i)⁻¹) * T
          * (S * diagonal (fun i => 1 - β ^ 2 * lam i) * T)).trace
        = (S * (diagonal (fun i => (1 + β * lam i)⁻¹) * (T * S)
          * diagonal (fun i => 1 - β ^ 2 * lam i)) * T).trace := by simp only [mul_assoc]
      _ = (diagonal (fun i => (1 + β * lam i)⁻¹)
          * diagonal (fun i => 1 - β ^ 2 * lam i)).trace := by
        rw [hTS, mul_one, trace_mul_cycle, hTS, one_mul]
      _ = _ := by
        rw [diagonal_mul_diagonal, trace_diagonal]
        unfold Ellipsoid.halderStationarity
        exact Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul]
  rw [htr]
  refine ((Ellipsoid.halderLogDet_hasDerivAt hpos hβ).const_add
    (Real.log Q₁.det)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hβ] with b hb
  exact hlog b hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
