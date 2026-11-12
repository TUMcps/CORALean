module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedBetaFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedErrorOkFloat
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The float accumulation of the windows' errors follows the real recursion from above

The floats `β_j` of `Krylov.restartedBetaFloat` ([1, Sec. 7]) are nonnegative and each is above
`e^{μΔt_j} β_j' + √b ε_j` of the real recursion `Krylov.restarted_error_le_weighted` asks for:
`expUp` is above the exponential for an argument in range (`Krylov.restartedErrorOkFloat`), `sqrtUp`
above the root, products and sums are rounded up. Shared by `Krylov.restartedErrorBoundFloat_sound`
and `Krylov.windowErrorBoundFloat_sound`.

## Inputs
* `p` – Newton steps per root
* `q` – squarings of the exponential
* `c` – Lyapunov weight
* `Δt` – window lengths
* `ε` – local 2-norm errors of the windows
* `N` – number of windows
* `β` – accumulated bounds

## Hypotheses
* `hβ` – the bounds are those of `Krylov.restartedBetaFloat`
* `hok` – the weight was accepted, a squaring is made and every window is nonnegative and in range
* `hε0` – local errors nonnegative

## Conclusion
* window lengths nonnegative, the bounds nonnegative, and the real recursion holds

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

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- For a certified accumulation (`Krylov.restartedErrorOkFloat`) and nonnegative `ε_j`: `Δt_j ≥ 0`,
`β_j ≥ 0` and `e^{μΔt_j} β_j + √b ε_j ≤ β_{j+1}`, as reals. -/
theorem Krylov.restartedBetaFloat_spec (p q : ℕ) (c : Krylov.LyapunovCertificateFloat 𝕋)
    (Δt ε : ℕ → 𝕋) (N : ℕ) (β : ℕ → 𝕋)
    (hβ : β = Krylov.restartedBetaFloat q (sqrtUp p c.upper) c.rate Δt ε)
    (hok : Krylov.restartedErrorOkFloat q c Δt N = true)
    (hε0 : ∀ j < N, 0 ≤ toReal (ε j)) : -- --- CONCL ---
    (∀ j < N, 0 ≤ toReal (Δt j)) ∧ (∀ j ≤ N, 0 ≤ toReal (β j)) ∧
    (∀ j < N, Real.exp (toReal c.rate * toReal (Δt j)) * toReal (β j) +
      Real.sqrt (toReal c.upper) * toReal (ε j) ≤ toReal (β (j + 1))) := by -- --- PROOF ---
  subst hβ
  unfold Krylov.restartedErrorOkFloat at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨_, hq⟩, hall⟩ := hok
  have hΔt : ∀ j < N, 0 ≤ toReal (Δt j) := fun j hj => by
    have := toReal_le_of_le (hall j hj).1
    rwa [toReal_zero] at this
  have hcap := fun j hj => (hall j hj).2
  set root := sqrtUp p c.upper with hroot
  set β : ℕ → ℝ := fun j => toReal (Krylov.restartedBetaFloat q root c.rate Δt ε j) with hβ
  have hrootle : Real.sqrt (toReal c.upper) ≤ toReal root := le_sqrtUp p c.upper
  -- the exponential's argument is in range, so `expUp` is above `e^{μΔt}`
  have hexp : ∀ j < N, Real.exp (toReal c.rate * toReal (Δt j)) ≤
      toReal (expUp q (mulUp c.rate (Δt j))) := by
    intro j hj
    have hcapR : toReal (mulUp c.rate (Δt j)) ≤ 2 ^ q / 2 := by
      have h1 := toReal_le_of_le (hcap j hj)
      have h2 := nsmulDown_le (2 ^ (q - 1)) (FloatOps.one : 𝕋)
      rw [toReal_one, mul_one] at h2
      refine h1.trans (h2.trans (le_of_eq ?_))
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp [pow_succ]
    exact (Real.exp_le_exp.2 (mul_le_mulUp c.rate (Δt j))).trans (le_expUp q _ hcapR)
  -- one step of the bound
  have hstep : ∀ j < N, 0 ≤ β j → Real.exp (toReal c.rate * toReal (Δt j)) * β j +
      Real.sqrt (toReal c.upper) * toReal (ε j) ≤ β (j + 1) := by
    intro j hj hβj
    have h1 := add_le_addUp (mulUp (expUp q (mulUp c.rate (Δt j)))
      (Krylov.restartedBetaFloat q root c.rate Δt ε j)) (mulUp root (ε j))
    have h2 := mul_le_mulUp (expUp q (mulUp c.rate (Δt j)))
      (Krylov.restartedBetaFloat q root c.rate Δt ε j)
    have h3 := mul_le_mulUp root (ε j)
    have h4 := mul_le_mul_of_nonneg_right (hexp j hj) hβj
    have h5 := mul_le_mul_of_nonneg_right hrootle (hε0 j hj)
    simp only [hβ, Krylov.restartedBetaFloat] at hβj ⊢
    linarith
  -- the bounds are nonnegative, by induction
  have hnn : ∀ j ≤ N, 0 ≤ β j := by
    intro j
    induction j with
    | zero => intro _; simp [hβ, Krylov.restartedBetaFloat, toReal_zero]
    | succ j ih =>
      intro hj
      have h := hstep j (by omega) (ih (by omega))
      have h6 := mul_nonneg (Real.exp_pos (toReal c.rate * toReal (Δt j))).le (ih (by omega))
      have h7 := mul_nonneg (Real.sqrt_nonneg (toReal c.upper)) (hε0 j (by omega))
      linarith
  exact ⟨hΔt, hnn, fun j hj => hstep j hj (hnn j hj.le)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
