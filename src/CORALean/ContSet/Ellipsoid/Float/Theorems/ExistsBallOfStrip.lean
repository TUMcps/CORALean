import CORALean.Global.EuclideanNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# A point of the unit ball in a strip, in the factored Gollamudi ellipsoid

The coefficient-space core of the float `intersectStripGollamudi`, for one strip. A factor vector
`u` with `‖u‖₂ ≤ 1` and `|vᵀ u - δ| ≤ φ` satisfies the Gollamudi combination
`(1 - λ)‖u‖₂² + λ (vᵀ u - δ)² ≤ 1 - λ + λ φ²`, which completes (with `ν = vᵀ v`,
`s = 1 - λ + λ ν`, the centre `κ v`, `κ = λ δ / s`, and `d = u - κ v`) to

  `(1 - λ)‖d‖₂² + λ (vᵀ d)² ≤ σ² = 1 - λ + λ φ² - λ (1 - λ) δ² / s`.

That is the ellipsoid of shape `σ² M⁻¹`, `M = (1 - λ) I + λ v vᵀ`, the real layer's
`σ² invQ⁻¹` read through `G` when `Q = G Gᵀ`. Its generator `N = α I + β v vᵀ` is not a computed
square root: any `α` and `γ = α + β ν`, both positive, with `σ² ≤ α² (1 - λ)` (the directions
across `v`) and `σ² ≤ γ² s` (the direction of `v`) will do, for any upper bound `S` of `σ²` in
their place. The factor is then explicit, `w = α⁻¹ (d - (β (vᵀ d) / γ) v)`, and its squared length
is `(γ² ‖d‖₂² - 2 β γ (vᵀ d)² + β² ν (vᵀ d)²) / (α² γ²)`, which the two conditions and
Cauchy–Schwarz bound by `1`. `v = 0` (`ν = 0`) and an empty strip (`S ≤ 0`) need no case of their
own in the statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix

variable {k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The squared length the two conditions bound: `γ² D - 2 β γ p² + β² ν p² ≤ α² γ²` from the
completed Gollamudi inequality, Cauchy–Schwarz `p² ≤ ν D`, and `γ = α + β ν`. -/
theorem Ellipsoid.aux_strip_factor_le {D p ν lam α β S : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1)
    (hD : 0 ≤ D) (hν : 0 ≤ ν) (hCS : p ^ 2 ≤ ν * D) (hα : 0 < α) (hγ : 0 < α + β * ν)
    (hkey : (1 - lam) * D + lam * p ^ 2 ≤ S) (hSα : S ≤ α ^ 2 * (1 - lam))
    (hSγ : S ≤ (α + β * ν) ^ 2 * (1 - lam + lam * ν)) :
    (α + β * ν) ^ 2 * D - 2 * β * (α + β * ν) * p ^ 2 + β ^ 2 * ν * p ^ 2
      ≤ α ^ 2 * (α + β * ν) ^ 2 := by -- --- PROOF ---
  set γ := α + β * ν with hγdef
  have hl : 0 < 1 - lam := by linarith
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  rcases le_or_gt S 0 with hS | hS
  · -- an empty strip, or one touching in the centre: `d = 0`
    have hD0 : D = 0 := by nlinarith
    have hp0 : p ^ 2 = 0 := by rw [hD0, mul_zero] at hCS; linarith
    rw [hD0, hp0]
    nlinarith [sq_nonneg (α * γ)]
  rcases eq_or_lt_of_le hν with hν0 | hνpos
  · -- `v = 0`: `γ = α`, and only the directions across `v` remain
    rw [← hν0] at hCS hγdef hSγ
    have hp0 : p ^ 2 = 0 := by rw [zero_mul] at hCS; linarith
    have hγα : γ = α := by rw [hγdef]; ring
    rw [hp0, hγα, ← hν0]
    have hDα : (1 - lam) * D ≤ (1 - lam) * α ^ 2 := by
      have := mul_nonneg h0 hp2
      linarith
    have hDα' : D ≤ α ^ 2 := le_of_mul_le_mul_left hDα (by linarith)
    have := mul_le_mul_of_nonneg_left hDα' (sq_nonneg α)
    linarith
  · -- `ν > 0`: with `ν γ² D - ν (2 β γ - β² ν) p² = γ² (ν D - p²) + α² p²`, each part weighted
    have hX : 0 ≤ ν * D - p ^ 2 := by linarith
    have hγ2 : 0 < γ ^ 2 := by positivity
    have hα2 : 0 < α ^ 2 := by positivity
    -- `ν (S L - α² γ² ((1-λ) D + λ p²)) ≤ - α² p² (γ² s - S) ≤ 0`
    have e1 : S * γ ^ 2 * (ν * D - p ^ 2) ≤ α ^ 2 * (1 - lam) * γ ^ 2 * (ν * D - p ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSα hγ2.le) hX
    have e2 : S * α ^ 2 * p ^ 2 ≤ γ ^ 2 * (1 - lam + lam * ν) * α ^ 2 * p ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSγ hα2.le) hp2
    have e3 : α ^ 2 * γ ^ 2 * ν * ((1 - lam) * D + lam * p ^ 2) ≤ α ^ 2 * γ ^ 2 * ν * S :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have hL : ν * S * (γ ^ 2 * D - 2 * β * γ * p ^ 2 + β ^ 2 * ν * p ^ 2)
        ≤ ν * S * (α ^ 2 * γ ^ 2) := by
      have hid : ν * S * (γ ^ 2 * D - 2 * β * γ * p ^ 2 + β ^ 2 * ν * p ^ 2)
          = S * γ ^ 2 * (ν * D - p ^ 2) + S * α ^ 2 * p ^ 2 := by rw [hγdef]; ring
      have hid2 : α ^ 2 * γ ^ 2 * ν * ((1 - lam) * D + lam * p ^ 2)
          = α ^ 2 * (1 - lam) * γ ^ 2 * (ν * D - p ^ 2)
            + γ ^ 2 * (1 - lam + lam * ν) * α ^ 2 * p ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_left hL (mul_pos hνpos hS)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.exists_ball_of_strip {v u : Vec ℝ k} {δ φ lam α β S : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam < 1) (hu : ‖u‖₂ ≤ 1) (hstrip : |v ⬝ᵥ u - δ| ≤ φ)
    (hS : 1 - lam + lam * φ ^ 2 - lam * (1 - lam) * δ ^ 2 / (1 - lam + lam * (v ⬝ᵥ v)) ≤ S)
    (hα : 0 < α) (hγ : 0 < α + β * (v ⬝ᵥ v)) (hSα : S ≤ α ^ 2 * (1 - lam))
    (hSγ : S ≤ (α + β * (v ⬝ᵥ v)) ^ 2 * (1 - lam + lam * (v ⬝ᵥ v))) :
    ∃ w : Vec ℝ k, ‖w‖₂ ≤ 1 ∧ u = (lam * δ / (1 - lam + lam * (v ⬝ᵥ v))) • v + α • w
      + (β * (v ⬝ᵥ w)) • v := by -- --- PROOF ---
  set ν := v ⬝ᵥ v with hν
  set γ := α + β * ν with hγdef
  have hν0 : 0 ≤ ν := by rw [hν, dotProduct_self]; positivity
  have hs0 : 0 < 1 - lam + lam * ν := by nlinarith
  set κ := lam * δ / (1 - lam + lam * ν) with hκdef
  have hκ : κ * (1 - lam + lam * ν) = lam * δ := by rw [hκdef]; field_simp
  -- the factor vector from the centre `κ v`
  set d := u - κ • v with hd
  have hud : u = d + κ • v := by rw [hd]; abel
  set D := d ⬝ᵥ d with hDdef
  set p := v ⬝ᵥ d with hpdef
  have hD0 : 0 ≤ D := by rw [hDdef, dotProduct_self]; positivity
  clear_value κ
  have hCS : p ^ 2 ≤ ν * D := by
    have h := abs_dotProduct_le_norm₂_mul_norm₂ v d
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, ← dotProduct_self, ← dotProduct_self] at h2
    exact h2
  -- the Gollamudi combination, completed at `κ v`
  have huu : u ⬝ᵥ u ≤ 1 := by
    rw [dotProduct_self]; nlinarith [norm₂_nonneg u]
  have huu' : u ⬝ᵥ u = D + 2 * κ * p + κ ^ 2 * ν := by
    rw [hud]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm d v]
    ring
  have hvu : v ⬝ᵥ u = p + κ * ν := by
    rw [hud, dotProduct_add, dotProduct_smul, smul_eq_mul]
  -- the strip, squared
  have hsq : (v ⬝ᵥ u - δ) ^ 2 ≤ φ ^ 2 := sq_le_sq' (abs_le.mp hstrip).1 (abs_le.mp hstrip).2
  have hkey : (1 - lam) * D + lam * p ^ 2 ≤ S := by
    have hcomb : (1 - lam) * (u ⬝ᵥ u) + lam * (v ⬝ᵥ u - δ) ^ 2 ≤ 1 - lam + lam * φ ^ 2 := by
      have c1 := mul_le_mul_of_nonneg_left huu (by linarith : (0 : ℝ) ≤ 1 - lam)
      have c2 := mul_le_mul_of_nonneg_left hsq h0
      linarith
    -- the cross terms `2 p (κ s - λ δ)` vanish
    have hid : (1 - lam) * (u ⬝ᵥ u) + lam * (v ⬝ᵥ u - δ) ^ 2
        = (1 - lam) * D + lam * p ^ 2 + (1 - lam) * δ * κ := by
      rw [huu', hvu]
      linear_combination (2 * p + κ * ν - δ) * hκ
    have hc : lam * (1 - lam) * δ ^ 2 / (1 - lam + lam * ν) = (1 - lam) * δ * κ := by
      rw [hκdef]; ring
    linarith
  have hL := Ellipsoid.aux_strip_factor_le h0 h1 hD0 hν0 hCS hα hγ hkey hSα hSγ
  -- the factor, explicitly
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hα0 : α ≠ 0 := hα.ne'
  refine ⟨α⁻¹ • (d - (β * p / γ) • v), ?_, ?_⟩
  · -- its squared length is the bounded quotient
    have hww : (α⁻¹ • (d - (β * p / γ) • v)) ⬝ᵥ (α⁻¹ • (d - (β * p / γ) • v))
        = (γ ^ 2 * D - 2 * β * γ * p ^ 2 + β ^ 2 * ν * p ^ 2) / (α ^ 2 * γ ^ 2) := by
      simp only [smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, smul_eq_mul,
        dotProduct_comm d v, ← hDdef, ← hpdef, ← hν]
      field_simp
      ring
    have h1' : (α⁻¹ • (d - (β * p / γ) • v)) ⬝ᵥ (α⁻¹ • (d - (β * p / γ) • v)) ≤ 1 := by
      rw [hww, div_le_one (by positivity)]
      exact hL
    rw [dotProduct_self, ← one_pow 2] at h1'
    exact (pow_le_pow_iff_left₀ (norm₂_nonneg _) zero_le_one two_ne_zero).mp h1'
  · -- and `N w = d`, since `vᵀ w = p / γ`
    have hvw : v ⬝ᵥ (α⁻¹ • (d - (β * p / γ) • v)) = p / γ := by
      simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul, ← hpdef, ← hν]
      field_simp
      rw [hγdef]; ring
    rw [hvw]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hd]
    field_simp
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
