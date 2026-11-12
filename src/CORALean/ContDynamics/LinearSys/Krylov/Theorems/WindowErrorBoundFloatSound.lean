module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.WindowErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.WindowErrorOkFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.LyapunovCertificateFloatSound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.RestartedBetaFloatSpec
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.RestartedErrorLeWeightedInside
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# The error bound inside a restart window is a bound

[1, Sec. 7] at every time of a window: with exact steps `v^{[j+1]} = e^{Δt_j A} v^{[j]}`,
approximate iterates `w^{[j+1]} = S_j w^{[j]}` from the same start, local 2-norm errors
`‖e^{Δt_j A} w^{[j]} - w^{[j+1]}‖₂ ≤ ε_j`, and in window `N` an approximate trajectory `W` with
`‖e^{sA} w^{[N]} - W(s)‖₂ ≤ ε_N` for every `s` of the window, the float
`Krylov.windowErrorBoundFloat` of an accepted weight bounds `‖e^{sA} v^{[N]} - W(s)‖₂` at every
such `s`. The floats are above the real recursion (`Krylov.restartedBetaFloat_spec`), the rate is
nonpositive (it is tested by `Krylov.windowErrorOkFloat`) and
`Krylov.restarted_error_le_weighted_inside` applies; `1/√a` is below the root of `1/a` rounded up.

## Inputs
* `p` – Newton steps per root
* `q` – squarings of the exponential
* `A` – matrix
* `P` – symmetric weight
* `L` – factor of `P - aI`
* `a` – shift
* `Δt` – lengths of the finished windows
* `ε` – local 2-norm errors of the windows
* `N` – number of finished windows
* `T` – length of window `N`
* `v` – exact iterates
* `w` – approximate iterates
* `S` – approximate step maps
* `W` – approximate trajectory inside window `N`

## Hypotheses
* `hok` – the weight was accepted, a squaring is made, every finished window is nonnegative and in
  range, and the rate is nonpositive
* `hv` – exact iterates follow the exact steps
* `hw` – approximate iterates follow the approximate steps
* `h0` – both start at the same vector
* `hloc` – local errors of the finished windows within the bounds
* `hin` – local error of window `N` within `ε_N` at every time of it

## Conclusion
* at every time of window `N` the 2-norm error is at most the float bound

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

/-- `‖e^{sA} v^{[N]} - W(s)‖₂ ≤ windowErrorBoundFloat` for `0 ≤ s ≤ T`, for an accepted weight. -/
theorem Krylov.windowErrorBoundFloat_sound (p q : ℕ) (A P L : Mat 𝕋 n n) (a : 𝕋)
    (Δt ε : ℕ → 𝕋) (N : ℕ) (T : ℝ)
    (hok : Krylov.windowErrorOkFloat q (Krylov.lyapunovCertificateFloat A P L a) Δt N = true)
    (v w : ℕ → Vec ℝ n) (S : ℕ → Vec ℝ n → Vec ℝ n) (W : ℝ → Vec ℝ n)
    (hv : ∀ j < N, v (j + 1) = exp (toReal (Δt j) • toRealMat A) *ᵥ v j)
    (hw : ∀ j < N, w (j + 1) = S j (w j)) (h0 : v 0 = w 0)
    (hloc : ∀ j < N,
      ‖exp (toReal (Δt j) • toRealMat A) *ᵥ w j - S j (w j)‖₂ ≤ toReal (ε j))
    (hin : ∀ s, 0 ≤ s → s ≤ T →
      ‖exp (s • toRealMat A) *ᵥ w N - W s‖₂ ≤ toReal (ε N)) : -- --- CONCL ---
    ∀ s, 0 ≤ s → s ≤ T → ‖exp (s • toRealMat A) *ᵥ v N - W s‖₂ ≤
      toReal (Krylov.windowErrorBoundFloat p q (Krylov.lyapunovCertificateFloat A P L a) Δt ε
        N) := by -- --- PROOF ---
  intro s hs0 hsT
  set c := Krylov.lyapunovCertificateFloat A P L a with hc
  unfold Krylov.windowErrorOkFloat at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hok, hrate⟩ := hok
  have hrate' : toReal c.rate ≤ 0 := by
    have := toReal_le_of_le hrate
    rwa [toReal_zero] at this
  have hcok : c.ok = true := by
    unfold Krylov.restartedErrorOkFloat at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1
  -- the local errors are nonnegative, the float recursion is above the real one
  have hε0 : ∀ j < N, 0 ≤ toReal (ε j) := fun j hj => (norm₂_nonneg _).trans (hloc j hj)
  have hεN : 0 ≤ toReal (ε N) := (norm₂_nonneg _).trans (hin s hs0 hsT)
  obtain ⟨hΔt, hnn, hstep⟩ := Krylov.restartedBetaFloat_spec p q c Δt ε N _ rfl hok hε0
  obtain ⟨hS, ha0, hb0, ha, hb, hPA⟩ := Krylov.lyapunovCertificateFloat_sound A P L a hcok
  set root := sqrtUp p c.upper with hroot
  have hrootle : Real.sqrt (toReal c.upper) ≤ toReal root := le_sqrtUp p c.upper
  have hmain := Krylov.restarted_error_le_weighted_inside (toRealMat A) (toRealMat P)
    (toReal c.rate) (toReal c.lower) (toReal c.upper) hS hPA ha hb ha0 hrate' N
    (fun j => toReal (Δt j)) T hΔt v w S W (fun j => toReal (ε j))
    (fun j => toReal (Krylov.restartedBetaFloat q root c.rate Δt ε j)) hv hw h0 hloc
    (by simp [Krylov.restartedBetaFloat, toReal_zero]) hstep
    (hnn N le_rfl) hin s hs0 hsT
  -- the float bound: `1/√a` below the root of `1/a` rounded up, `β_N + √b ε_N` below its float
  refine hmain.trans ?_
  have hsa : 0 < Real.sqrt (toReal c.lower) := Real.sqrt_pos.2 ha0
  have hinv : (Real.sqrt (toReal c.lower))⁻¹ ≤ toReal (sqrtUp p (divUp FloatOps.one c.lower)) := by
    have h1 := div_le_divUp (FloatOps.one : 𝕋) c.lower ha0
    rw [toReal_one] at h1
    calc (Real.sqrt (toReal c.lower))⁻¹ = Real.sqrt (toReal c.lower)⁻¹ := (Real.sqrt_inv _).symm
      _ ≤ Real.sqrt (toReal (divUp FloatOps.one c.lower)) :=
        Real.sqrt_le_sqrt (by rw [← one_div]; exact h1)
      _ ≤ _ := le_sqrtUp p _
  -- the sum `β_N + √b ε_N` is below its float
  have hsum : toReal (Krylov.restartedBetaFloat q root c.rate Δt ε N) +
      Real.sqrt (toReal c.upper) * toReal (ε N) ≤
      toReal (addUp (Krylov.restartedBetaFloat q root c.rate Δt ε N) (mulUp root (ε N))) := by
    have h1 := add_le_addUp (Krylov.restartedBetaFloat q root c.rate Δt ε N) (mulUp root (ε N))
    have h2 := mul_le_mulUp root (ε N)
    have h3 := mul_le_mul_of_nonneg_right hrootle hεN
    linarith
  have hsum0 : 0 ≤ toReal (Krylov.restartedBetaFloat q root c.rate Δt ε N) +
      Real.sqrt (toReal c.upper) * toReal (ε N) :=
    add_nonneg (hnn N le_rfl) (mul_nonneg (Real.sqrt_nonneg _) hεN)
  rw [div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left hinv hsum0).trans
    ((mul_le_mul_of_nonneg_right hsum (by exact (inv_nonneg.2 hsa.le).trans hinv)).trans
      (mul_le_mulUp _ _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
