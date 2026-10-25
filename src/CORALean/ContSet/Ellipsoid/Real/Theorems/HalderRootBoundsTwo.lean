module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStationarityTwo
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStationarityStrictAntiOn
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Bounds on the root of Halder's stationarity equation for two eigenvalues

[1, Eq. 25]: for `d = 2` the positive root `β₊` of [1, Eq. 18] lies strictly between the
abscissa of the minimum of the cubic `p₃`, `(√((λ₁+λ₂)(λ₁+λ₂+6λ₁λ₂)) − (λ₁+λ₂)) / (6λ₁λ₂)`,
and the smaller of the positive zeros `(λⱼ + √(λⱼ(λⱼ+8)))/(2λⱼ)` of the parabolas that
`p₃` reduces to when `λᵢ = 0`. Both follow from the stationarity function being strictly
decreasing: `p₃` is negative at the first bound and positive at the others.

## Inputs
* `l₁` – first eigenvalue
* `l₂` – second eigenvalue
* `r` – root of the stationarity equation

## Hypotheses
* `h₁` – `0 < l₁`
* `h₂` – `0 < l₂`
* `hr` – `0 < r`
* `hroot` – the stationarity function vanishes at `r`

## Conclusion
* `r` lies between the two printed bounds

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC), 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_upper {a c r : ℝ} (ha : 0 < a) (hc : 0 < c) (hr : 0 < r)
    (hp : 2 * (a * c) * r ^ 3 + (a + c) * r ^ 2 - (a + c) * r - 2 = 0) : -- --- CONCL ---
    r < (a + Real.sqrt (a * (a + 8))) / (2 * a) := by -- --- PROOF ---
  -- `ρ` is the positive zero of the parabola `a x² − a x − 2`, and exceeds `1`
  set S := Real.sqrt (a * (a + 8)) with hS
  have hS2 : S ^ 2 = a * (a + 8) := Real.sq_sqrt (by positivity)
  have haS : a < S := by
    rw [hS]; exact Real.lt_sqrt ha.le |>.2 (by nlinarith)
  set ρ := (a + S) / (2 * a) with hρ
  have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ (by positivity)]; linarith
  have hρq : a * ρ ^ 2 - a * ρ - 2 = 0 := by
    rw [hρ]; field_simp; nlinarith [hS2]
  -- past `ρ` the cubic is positive, so the root cannot be there
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : 0 ≤ a * (r ^ 2 - r) - a * (ρ ^ 2 - ρ) := by
    have : 0 ≤ (r - ρ) * (r + ρ - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg ha.le this]
  nlinarith [mul_pos (mul_pos ha hc) (pow_pos hr 3), mul_pos hc hr, mul_pos (mul_pos hc hr)
    (sub_pos.2 (hρ1.trans_le hcon))]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 25]: the root of [1, Eq. 18] at `d = 2` lies between the two printed bounds. -/
theorem Ellipsoid.halderRoot_bounds_two {l₁ l₂ r : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂)
    (hr : 0 < r) (hroot : Ellipsoid.halderStationarity ![l₁, l₂] r = 0) : -- --- CONCL ---
    (Real.sqrt ((l₁ + l₂) * (l₁ + l₂ + 6 * (l₁ * l₂))) - (l₁ + l₂)) / (6 * (l₁ * l₂)) < r
    ∧ r < min ((l₁ + Real.sqrt (l₁ * (l₁ + 8))) / (2 * l₁))
        ((l₂ + Real.sqrt (l₂ * (l₂ + 8))) / (2 * l₂)) := by -- --- PROOF ---
  have hlam : ∀ i, 0 < (![l₁, l₂] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [h₁, h₂]
  have hanti := Ellipsoid.halderStationarity_strictAntiOn hlam
  -- the cubic vanishes at the root
  have hp : 2 * (l₁ * l₂) * r ^ 3 + (l₁ + l₂) * r ^ 2 - (l₁ + l₂) * r - 2 = 0 := by
    rw [Ellipsoid.halderStationarity_two h₁ h₂ hr.le] at hroot
    have : 0 < (1 + r * l₁) * (1 + r * l₂) := by positivity
    have := (div_eq_zero_iff.1 hroot).resolve_right this.ne'
    linarith
  have hp'' := hp
  set s := l₁ + l₂ with hs
  set p := l₁ * l₂ with hp'
  have hspos : 0 < s := by positivity
  have hppos : 0 < p := by positivity
  constructor
  · -- the abscissa `b` of the cubic's minimum lies left of the root, where the cubic is negative
    set T := Real.sqrt (s * (s + 6 * p)) with hT
    have hT2 : T ^ 2 = s * (s + 6 * p) := Real.sq_sqrt (by positivity)
    have hTs : s < T := by
      rw [hT]; exact Real.lt_sqrt (by positivity) |>.2 (by nlinarith)
    set b := (T - s) / (6 * p) with hb
    have hb0 : 0 < b := div_pos (by linarith) (by positivity)
    have hq : 6 * p * b ^ 2 + 2 * s * b - s = 0 := by
      rw [hb]; field_simp; nlinarith [hT2]
    have hb1 : b < 1 / 2 := by nlinarith [mul_pos hppos (pow_pos hb0 2)]
    have hneg : 2 * p * b ^ 3 + s * b ^ 2 - s * b - 2 < 0 := by nlinarith [mul_pos hspos hb0]
    by_contra hcon
    rw [not_lt] at hcon
    have h1 := hanti.antitoneOn (Set.mem_Ici.2 hr.le) (Set.mem_Ici.2 hb0.le) hcon
    rw [hroot, Ellipsoid.halderStationarity_two h₁ h₂ hb0.le] at h1
    have : 0 < (1 + b * l₁) * (1 + b * l₂) := by positivity
    rw [hs, hp'] at hneg
    exact absurd h1 (not_le.2 (div_pos (by linarith) this))
  · -- below the larger of the two roots of the one-generator parabolas the cubic is positive
    refine lt_min ?_ ?_
    · exact Ellipsoid.aux_upper h₁ h₂ hr hp''
    · exact Ellipsoid.aux_upper h₂ h₁ hr (by rw [mul_comm l₂ l₁, add_comm l₂ l₁]; exact hp'')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
