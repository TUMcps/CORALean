module

public import CORALean.Global.AddDivSqrtTwoLeSqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# A regular polygon has a direction within half a step of any vector

Among the `N` directions `(cos φₖ, sin φₖ)`, `φₖ = 2πk/N`, one makes an angle of at most `π/N`
with any `v`, so its component of `v` is at least `cos(π/N) ‖v‖₂`. This is what puts the polygon
`{x | cos φₖ x₁ + sin φₖ x₂ ≤ R cos(π/N)}` inside the disk of radius `R`. A second statement covers
coefficients stored with an error `ε`: the component falls by at most `√2 ε ‖v‖₂`.

## Inputs
* `N` – number of sides
* `x` – first coordinate of `v`
* `y` – second coordinate of `v`

## Hypotheses
* `hN` – the polygon has a side

## Conclusion
* some direction has a component of `v` of at least `cos(π/N) ‖v‖₂`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `1`-norm of the plane against its Euclidean norm. -/
private theorem aux_abs_add_abs_le_sqrt_two_mul (v₁ v₂ : ℝ) :
    |v₁| + |v₂| ≤ √2 * √(v₁ ^ 2 + v₂ ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (|v₁| - |v₂|), sq_abs v₁, sq_abs v₂]

/-- The angle `2πm/N` of the multiple `m` nearest to `θ` is within `π/N` of `θ`. -/
private theorem aux_abs_angle_sub_le {N : ℕ} (hN : 0 < N) (θ : ℝ) : -- --- CONCL ---
    |2 * Real.pi * ⌊θ * N / (2 * Real.pi) + 1 / 2⌋ / N - θ| ≤ Real.pi / N := by -- --- PROOF ---
  set m : ℤ := ⌊θ * N / (2 * Real.pi) + 1 / 2⌋ with hm
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpi := Real.pi_pos
  have h1 : (m : ℝ) ≤ θ * N / (2 * Real.pi) + 1 / 2 := Int.floor_le _
  have h2 : θ * N / (2 * Real.pi) + 1 / 2 < m + 1 := Int.lt_floor_add_one _
  have hfac : 2 * Real.pi * m / N - θ = 2 * Real.pi / N * (m - θ * N / (2 * Real.pi)) := by
    field_simp
  have hhalf : |(m : ℝ) - θ * N / (2 * Real.pi)| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  rw [hfac, abs_mul, abs_of_pos (by positivity)]
  calc 2 * Real.pi / N * |(m : ℝ) - θ * N / (2 * Real.pi)| ≤ 2 * Real.pi / N * (1 / 2) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = Real.pi / N := by ring

/-- The direction `m` reduced modulo `N` is the direction `m`: the angles differ by whole turns. -/
private theorem aux_dir_mod {N : ℕ} (hN : 0 < N) (m : ℤ) (x y : ℝ) : -- --- CONCL ---
    ∃ k : Fin N, Real.cos (2 * Real.pi * k / N) * x + Real.sin (2 * Real.pi * k / N) * y =
      Real.cos (2 * Real.pi * m / N) * x +
        Real.sin (2 * Real.pi * m / N) * y := by -- --- PROOF ---
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmod : 0 ≤ m % N := Int.emod_nonneg _ hNz
  have hlt : m % N < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
  refine ⟨⟨(m % N).toNat, by omega⟩, ?_⟩
  -- `m = (m % N) + N (m / N)`, so the two angles differ by `m / N` turns
  have hk : (((m % N).toNat : ℕ) : ℝ) = ((m % N : ℤ) : ℝ) := by
    have : (((m % N).toNat : ℕ) : ℤ) = m % N := Int.toNat_of_nonneg hmod
    exact_mod_cast this
  have hdiv : (m : ℝ) = ((m % N : ℤ) : ℝ) + (m / N : ℤ) * N := by
    have h' : ((m % N : ℤ) : ℝ) + (N : ℝ) * ((m / N : ℤ) : ℝ) = m := by
      exact_mod_cast Int.emod_add_mul_ediv m N
    linarith
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hang : 2 * Real.pi * m / N =
      2 * Real.pi * (((m % N).toNat : ℕ) : ℝ) / N + ((m / N : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hk, hdiv]; field_simp
  rw [hang, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Some direction of the regular `N`-gon has the component `cos(π/N) ‖(x, y)‖₂` or more. -/
theorem exists_regularPolygon_dot_ge {N : ℕ} (hN : 0 < N) (x y : ℝ) : -- --- CONCL ---
    ∃ k : Fin N, Real.cos (Real.pi / N) * √(x ^ 2 + y ^ 2) ≤
      Real.cos (2 * Real.pi * k / N) * x + Real.sin (2 * Real.pi * k / N) * y := by -- --- PROOF ---
  -- write `v` in polar form `‖z‖ (cos θ, sin θ)` and take the multiple `m` of the step nearest `θ`
  set z : ℂ := ⟨x, y⟩ with hz
  have hnorm : ‖z‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp [hz, sq]
  have hx : x = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
  have hy : y = ‖z‖ * Real.sin z.arg := (Complex.norm_mul_sin_arg z).symm
  set θ := z.arg
  set m : ℤ := ⌊θ * N / (2 * Real.pi) + 1 / 2⌋ with hm
  -- the direction `m` is within `π/N` of `v`, so its cosine against `v` is at least `cos(π/N)`
  have hcos : Real.cos (Real.pi / N) ≤ Real.cos (2 * Real.pi * m / N - θ) := by
    rw [← Real.cos_abs (2 * Real.pi * m / N - θ)]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) ?_ (aux_abs_angle_sub_le hN θ)
    exact div_le_self Real.pi_pos.le (by exact_mod_cast hN)
  obtain ⟨k, hk⟩ := aux_dir_mod hN m x y
  refine ⟨k, ?_⟩
  rw [hk, hnorm.symm, hx, hy]
  have hdot : Real.cos (2 * Real.pi * m / N) * (‖z‖ * Real.cos θ) +
      Real.sin (2 * Real.pi * m / N) * (‖z‖ * Real.sin θ) =
      ‖z‖ * Real.cos (2 * Real.pi * m / N - θ) := by
    rw [Real.cos_sub]; ring
  rw [hdot]
  exact (mul_le_mul_of_nonneg_left hcos (norm_nonneg _)).trans_eq' (by ring)

/-- The same with coefficients within `ε` of the directions: the bound falls by `√2 ε ‖v‖₂`. -/
theorem exists_regularPolygon_dot_ge_of_abs_sub_le {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (a b : Fin N → ℝ) (ha : ∀ k : Fin N, |a k - Real.cos (2 * Real.pi * k / N)| ≤ ε)
    (hb : ∀ k : Fin N, |b k - Real.sin (2 * Real.pi * k / N)| ≤ ε) (v₁ v₂ : ℝ) : -- --- CONCL ---
    ∃ k : Fin N, (Real.cos (Real.pi / N) - √2 * ε) * √(v₁ ^ 2 + v₂ ^ 2) ≤
      a k * v₁ + b k * v₂ := by -- --- PROOF ---
  obtain ⟨k, hk⟩ := exists_regularPolygon_dot_ge hN v₁ v₂
  refine ⟨k, ?_⟩
  set c := Real.cos (2 * Real.pi * k / N)
  set s := Real.sin (2 * Real.pi * k / N)
  have h1 := aux_abs_add_abs_le_sqrt_two_mul v₁ v₂
  have hε : 0 ≤ ε := (abs_nonneg _).trans (ha k)
  -- each coefficient error costs at most `ε |vᵢ|`
  have e1 : (a k - c) * v₁ ≥ -(ε * |v₁|) := by
    have h2 : |(a k - c) * v₁| ≤ ε * |v₁| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha k) (abs_nonneg _)
    linarith [neg_abs_le ((a k - c) * v₁)]
  have e2 : (b k - s) * v₂ ≥ -(ε * |v₂|) := by
    have h2 : |(b k - s) * v₂| ≤ ε * |v₂| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb k) (abs_nonneg _)
    linarith [neg_abs_le ((b k - s) * v₂)]
  have h3 : ε * (|v₁| + |v₂|) ≤ ε * (√2 * √(v₁ ^ 2 + v₂ ^ 2)) := mul_le_mul_of_nonneg_left h1 hε
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
