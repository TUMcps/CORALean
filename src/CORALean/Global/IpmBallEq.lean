module

public import CORALean.Global.IpmBall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# The interval of the ball predictor

[1, Eq. 6]: for the ball model [1, Eq. 3], [1, Eq. 4] (`ipmBall`) with `r, γ ≥ 0`,
`I(ϕ) = [cᵀϕ - (r‖ϕ‖ + γ), cᵀϕ + (r‖ϕ‖ + γ)]`, `‖ϕ‖ = √(ϕᵀϕ)`. Exactly that interval: the paper
shows the enclosure, `|ρᵀϕ| ≤ r‖ϕ‖` for `ϑ = c + ρ`, `‖ρ‖ ≤ r` (Cauchy-Schwarz); every point of it
is attained, `y = cᵀϕ + t(r‖ϕ‖ + γ)` at `ϑ = c + (tr/‖ϕ‖)ϕ`, `e = tγ`, `|t| ≤ 1`.

## Inputs
* `c` – center of the parameter ball
* `r` – radius of the parameter ball
* `γ` – noise bound
* `ϕ` – regressor

## Hypotheses
* `hr` – the radius is nonnegative
* `hγ` – the noise bound is nonnegative

## Conclusion
* the predictor set is the interval around the center's output with the ball's half width

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- Cauchy-Schwarz for the dot product, in square roots
theorem aux_abs_dotProduct_le (a b : Vec ℝ n) :
    |a ⬝ᵥ b| ≤ Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by -- --- PROOF ---
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have ha : 0 ≤ a ⬝ᵥ a := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [← Real.sqrt_mul ha, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  simpa [dotProduct, sq] using h


-- =======================================  MAIN THEOREM  ======================================= --

theorem ipmBall_eq (c : Vec ℝ n) (r γ : ℝ) (hr : 0 ≤ r) (hγ : 0 ≤ γ) (ϕ : Vec ℝ n) :
    ipmBall c r γ ϕ = Set.Icc (c ⬝ᵥ ϕ - (r * Real.sqrt (ϕ ⬝ᵥ ϕ) + γ))
      (c ⬝ᵥ ϕ + (r * Real.sqrt (ϕ ⬝ᵥ ϕ) + γ)) := by -- --- PROOF ---
  have hϕ : 0 ≤ ϕ ⬝ᵥ ϕ := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  ext y
  constructor
  · rintro ⟨ϑ, e, hϑ, he, rfl⟩
    -- `ϑᵀϕ = cᵀϕ + ρᵀϕ`, `|ρᵀϕ| ≤ ‖ρ‖‖ϕ‖ ≤ r‖ϕ‖`
    have hρ : |(ϑ - c) ⬝ᵥ ϕ| ≤ r * Real.sqrt (ϕ ⬝ᵥ ϕ) := by
      refine (aux_abs_dotProduct_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      calc Real.sqrt ((ϑ - c) ⬝ᵥ (ϑ - c)) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hϑ
        _ = r := Real.sqrt_sq hr
    have hsplit : ϑ ⬝ᵥ ϕ = c ⬝ᵥ ϕ + (ϑ - c) ⬝ᵥ ϕ := by rw [sub_dotProduct]; ring
    rw [abs_le] at hρ he
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    -- `y = cᵀϕ + t(r‖ϕ‖ + γ)` for some `t ∈ [-1, 1]`
    set w := r * Real.sqrt (ϕ ⬝ᵥ ϕ) + γ
    have hw : 0 ≤ w := by positivity
    rcases eq_or_lt_of_le hw with hw0 | hwpos
    · -- a degenerate interval: `y = cᵀϕ`
      refine ⟨c, 0, by simp; positivity, by simpa using hγ, ?_⟩
      simp; linarith
    set t := (y - c ⬝ᵥ ϕ) / w
    have ht : |t| ≤ 1 := by
      rw [abs_le]; constructor
      · rw [le_div_iff₀ hwpos]; linarith
      · rw [div_le_iff₀ hwpos]; linarith
    -- the regressor term reaches `tr‖ϕ‖` and the noise `tγ`
    rcases eq_or_lt_of_le hϕ with hϕ0 | hϕpos
    · -- `ϕ = 0`: the noise alone
      refine ⟨c, t * γ, by simp; positivity, ?_, ?_⟩
      · rw [abs_mul, abs_of_nonneg hγ]
        calc |t| * γ ≤ 1 * γ := mul_le_mul_of_nonneg_right ht hγ
          _ = γ := one_mul γ
      · have : w = γ := by simp [w, ← hϕ0]
        have hyt : y = c ⬝ᵥ ϕ + t * w := by simp only [t]; field_simp; ring
        rw [hyt, this]
    · -- `ϑ = c + (tr/‖ϕ‖)ϕ` lies in the ball and gives `ϑᵀϕ = cᵀϕ + tr‖ϕ‖`
      set s := Real.sqrt (ϕ ⬝ᵥ ϕ)
      have hs : 0 < s := Real.sqrt_pos.mpr hϕpos
      refine ⟨c + (t * r / s) • ϕ, t * γ, ?_, ?_, ?_⟩
      · simp only [add_sub_cancel_left, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        have hss : ϕ ⬝ᵥ ϕ = s ^ 2 := (Real.sq_sqrt hϕ).symm
        rw [hss]
        field_simp
        have ht2 : t ^ 2 ≤ 1 := by
          have := abs_le.mp ht; nlinarith
        nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg r)]
      · rw [abs_mul, abs_of_nonneg hγ]
        calc |t| * γ ≤ 1 * γ := mul_le_mul_of_nonneg_right ht hγ
          _ = γ := one_mul γ
      · have hss : ϕ ⬝ᵥ ϕ = s ^ 2 := (Real.sq_sqrt hϕ).symm
        have hyt : y = c ⬝ᵥ ϕ + t * w := by simp only [t]; field_simp; ring
        rw [hyt, add_dotProduct, smul_dotProduct, smul_eq_mul, hss]
        simp only [w]
        field_simp
        ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
