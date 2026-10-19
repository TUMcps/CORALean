module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Times
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# [1, Thm. 1] does not hold for models whose expansion point moves with `h`

[1, Thm. 1] asks `f, g ∈ Cⁿ⁺¹(D)` and remainders `O(hⁿ⁺¹)` of models around `x_h` on
`x_h + [-h, h]`, and concludes the same for `f·g` by [1, Def. 2], eq. (2.8). It states nothing
about the size of the polynomial parts, and the product remainder is
`B(Pₑ) + B(P_f)·I_g + B(P_g)·I_f + I_f·I_g`. With `D = ℝ`, `n = 1`, `f(x) = x²`, `g(x) = x`
and `x_h = 1/h`, over the normalized variable `x = x_h + h·t` the models are
`1/h² + 2t` with remainder `[0, h²]` and `1/h + h·t` with remainder `0`: both remainders are
`O(h²)`. The product's remainder has upper end at least `B(P_g)·I_f = (1/h + h)·h² ≥ h`,
which is not `O(h²)`. The models are Taylor models (`Encloses` is all the hypothesis asks of a
model here), and the theorem holds when `x_h` is fixed, since the polynomial's coefficients
are then bounded.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], eq. (2.8) for `f·g`: models around `x_h` of order `1` on `x_h + [-h, h]` with
remainders `O(h²)` give a product model with remainders `O(h²)`. They do not. -/
theorem Taylm.times_scaling_counterexample : -- --- CONCL ---
    ¬ ∀ (f g : ℝ → ℝ) (xh : ℝ → ℝ) (T₁ T₂ : ℝ → Taylm 1), ContDiff ℝ 2 f → ContDiff ℝ 2 g →
      (∀ h, 0 < h → h ≤ 1 → (T₁ h).maxOrder = 1 ∧ (T₂ h).maxOrder = 1
        ∧ (T₁ h).Encloses (fun t => f (xh h + h * t 0))
        ∧ (T₂ h).Encloses (fun t => g (xh h + h * t 0))) →
      (∃ C, ∀ h, 0 < h → h ≤ 1 →
        |(T₁ h).rem.inf| ≤ C * h ^ 2 ∧ |(T₁ h).rem.sup| ≤ C * h ^ 2
        ∧ |(T₂ h).rem.inf| ≤ C * h ^ 2 ∧ |(T₂ h).rem.sup| ≤ C * h ^ 2) →
      ∃ C, ∀ h, 0 < h → h ≤ 1 →
        |((T₁ h).times (T₂ h)).rem.inf| ≤ C * h ^ 2
          ∧ |((T₁ h).times (T₂ h)).rem.sup| ≤ C * h ^ 2 := by -- --- PROOF ---
  intro H
  -- the order-1 model of `(x_h + h t)²` and of `x_h + h t`, both at `x_h = 1/h`
  have hE1 : ∀ h : ℝ, 0 < h → (⟨[(1 / h ^ 2, fun _ => 0), (2, fun _ => 1)], ⟨0, h ^ 2⟩, 1⟩ :
      Taylm 1).Encloses (fun t => (fun x : ℝ => x ^ 2) ((fun h : ℝ => 1 / h) h + h * t 0)) := by
    intro h h0 t ht
    simp only [Taylm.poly, Taylm.polyOf_cons, Taylm.polyOf_nil, Taylm.monomial]
    simp
    have ht2 : t 0 ^ 2 ≤ 1 := by
      have := abs_le.mp (ht 0)
      nlinarith [this.1, this.2]
    constructor
    · field_simp
      nlinarith [sq_nonneg (h ^ 2 * t 0)]
    · field_simp
      nlinarith [mul_nonneg (pow_nonneg h0.le 4) (sub_nonneg.mpr ht2)]
  -- the order-1 model of `x_h + h t`, exact
  have hE2 : ∀ h : ℝ, 0 < h → (⟨[(1 / h, fun _ => 0), (h, fun _ => 1)], ⟨0, 0⟩, 1⟩ :
      Taylm 1).Encloses (fun t => id ((fun h : ℝ => 1 / h) h + h * t 0)) := by
    intro h h0 t ht
    simp only [Taylm.poly, Taylm.polyOf_cons, Taylm.polyOf_nil, Taylm.monomial]
    simp
  -- the hypotheses hold with `C = 1`, so the conclusion is asked of the product
  obtain ⟨C, hC⟩ := H (fun x => x ^ 2) id (fun h => 1 / h)
    (fun h => ⟨[(1 / h ^ 2, fun _ => 0), (2, fun _ => 1)], ⟨0, h ^ 2⟩, 1⟩)
    (fun h => ⟨[(1 / h, fun _ => 0), (h, fun _ => 1)], ⟨0, 0⟩, 1⟩)
    (ContDiff.pow (contDiff_id : ContDiff ℝ 2 (id : ℝ → ℝ)) 2) contDiff_id
    (fun h h0 _ => ⟨rfl, rfl, hE1 h h0, hE2 h h0⟩)
    ⟨1, fun h h0 h1 => by simp [abs_of_pos h0, h0.le]⟩
  -- the product's upper remainder is at least `h`
  have hge : ∀ h : ℝ, 0 < h → h ≤ ((⟨[(1 / h ^ 2, fun _ => 0), (2, fun _ => 1)], ⟨0, h ^ 2⟩, 1⟩ :
      Taylm 1).times ⟨[(1 / h, fun _ => 0), (h, fun _ => 1)], ⟨0, 0⟩, 1⟩).rem.sup := by
    intro h h0
    simp [Taylm.times, Taylm.mulTerms, Taylm.polyBounds, Taylm.termBounds, Taylm.degree,
      Interval.mulHi, Interval.mulLo, Pi.add_apply, Nat.ble]
    have h1 : 0 ≤ max (max 0 ((h⁻¹ + -|h|) * h ^ 2)) (max 0 ((h⁻¹ + |h|) * h ^ 2)) :=
      le_trans (le_max_left 0 _) (le_max_left _ _)
    have h2 := le_max_left (2 * h) 0
    linarith
  -- so `h ≤ C h²` for every `h ∈ (0, 1]`, which `h = 1/(|C| + 2)` refutes
  have hpos : (0 : ℝ) < |C| + 2 := by positivity
  have h0 : (0 : ℝ) < 1 / (|C| + 2) := by positivity
  have h1 : 1 / (|C| + 2) ≤ (1 : ℝ) := by
    rw [div_le_one hpos]
    linarith [abs_nonneg C]
  have hb := (hC _ h0 h1).2
  have hg := hge _ h0
  have hle : 1 / (|C| + 2) ≤ C * (1 / (|C| + 2)) ^ 2 :=
    le_trans hg (le_trans (le_abs_self _) hb)
  rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ hpos (by positivity)] at hle
  nlinarith [le_abs_self C, abs_nonneg C]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
