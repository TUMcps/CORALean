module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedErrorOkFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.LyapunovCertificateFloatSound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.RestartedBetaFloatSpec
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.RestartedErrorLeWeighted
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# The restarted Krylov error bound in a Lyapunov weight is a bound

[1, Sec. 7] in a Lyapunov weight: with the exact steps `v^{[j+1]} = e^{Δt_j A} v^{[j]}`,
approximate iterates `w^{[j+1]} = S_j w^{[j]}` from the same start, and local 2-norm errors
`‖e^{Δt_j A} w^{[j]} - w^{[j+1]}‖₂ ≤ ε_j`, the float `Krylov.restartedErrorBoundFloat` of an
accepted weight bounds `‖v^{[N]} - w^{[N]}‖₂`. Each float `β_{j+1}` is above
`e^{μΔt_j} β_j + √b ε_j` (`expUp` is above the exponential for an argument in range, `sqrtUp`
above the root, products and sums rounded up), so `Krylov.restarted_error_le_weighted` applies,
and `1/√a` is below the root of `1/a` rounded up.

## Inputs
* `p` – Newton steps per root
* `q` – squarings of the exponential
* `A` – matrix
* `P` – symmetric weight
* `L` – factor of `P - aI`
* `a` – shift
* `Δt` – window lengths
* `ε` – local 2-norm errors of the windows
* `N` – number of windows
* `v` – exact iterates
* `w` – approximate iterates
* `S` – approximate step maps

## Hypotheses
* `hok` – the weight was accepted, a squaring is made and every window is nonnegative and in range
* `hv` – exact iterates follow the exact steps
* `hw` – approximate iterates follow the approximate steps
* `h0` – both start at the same vector
* `hloc` – local errors within the bounds

## Conclusion
* the 2-norm error after `N` windows is at most the float bound

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

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `‖v^{[N]} - w^{[N]}‖₂ ≤ restartedErrorBoundFloat` for an accepted weight. -/
theorem Krylov.restartedErrorBoundFloat_sound (p q : ℕ) (A P L : Mat 𝕋 n n) (a : 𝕋)
    (Δt ε : ℕ → 𝕋) (N : ℕ)
    (hok : Krylov.restartedErrorOkFloat q (Krylov.lyapunovCertificateFloat A P L a) Δt N = true)
    (v w : ℕ → Vec ℝ n) (S : ℕ → Vec ℝ n → Vec ℝ n)
    (hv : ∀ j < N, v (j + 1) = exp (toReal (Δt j) • toRealMat A) *ᵥ v j)
    (hw : ∀ j < N, w (j + 1) = S j (w j)) (h0 : v 0 = w 0)
    (hloc : ∀ j < N,
      ‖exp (toReal (Δt j) • toRealMat A) *ᵥ w j - S j (w j)‖₂ ≤ toReal (ε j)) : -- --- CONCL ---
    ‖v N - w N‖₂ ≤
      toReal (Krylov.restartedErrorBoundFloat p q (Krylov.lyapunovCertificateFloat A P L a) Δt ε
        N) := by -- --- PROOF ---
  set c := Krylov.lyapunovCertificateFloat A P L a with hc
  have hcok : c.ok = true := by
    unfold Krylov.restartedErrorOkFloat at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1
  have hε0 : ∀ j < N, 0 ≤ toReal (ε j) := fun j hj => (norm₂_nonneg _).trans (hloc j hj)
  obtain ⟨hΔt, hnn, hstep⟩ := Krylov.restartedBetaFloat_spec p q c Δt ε N _ rfl hok hε0
  obtain ⟨hS, ha0, hb0, ha, hb, hPA⟩ := Krylov.lyapunovCertificateFloat_sound A P L a hcok
  set root := sqrtUp p c.upper with hroot
  set β : ℕ → ℝ := fun j => toReal (Krylov.restartedBetaFloat q root c.rate Δt ε j) with hβ
  -- the real theorem, then the final factor `1/√a`
  have hmain := Krylov.restarted_error_le_weighted (toRealMat A) (toRealMat P) (toReal c.rate)
    (toReal c.lower) (toReal c.upper) hS hPA ha hb ha0 N (fun j => toReal (Δt j)) hΔt v w S
    (fun j => toReal (ε j)) β hv hw h0 hloc (hnn 0 (Nat.zero_le _))
    hstep
  refine hmain.trans ?_
  have hsa : 0 < Real.sqrt (toReal c.lower) := Real.sqrt_pos.2 ha0
  have hinv : (Real.sqrt (toReal c.lower))⁻¹ ≤ toReal (sqrtUp p (divUp FloatOps.one c.lower)) := by
    have h1 := div_le_divUp (FloatOps.one : 𝕋) c.lower ha0
    rw [toReal_one] at h1
    calc (Real.sqrt (toReal c.lower))⁻¹ = Real.sqrt (toReal c.lower)⁻¹ := (Real.sqrt_inv _).symm
      _ ≤ Real.sqrt (toReal (divUp FloatOps.one c.lower)) :=
        Real.sqrt_le_sqrt (by rw [← one_div]; exact h1)
      _ ≤ _ := le_sqrtUp p _
  rw [div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left hinv (hnn N le_rfl)).trans (mul_le_mulUp _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
