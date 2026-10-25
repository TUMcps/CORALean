module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.CutShapeDetLe
public import CORALean.ContSet.Ellipsoid.Real.Theorems.CutShapePosDef
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq
public import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A cut at Goffin's depth shrinks the volume by a constant factor

[1, Lemma 4.4]: for `ε > 0` there is `κ_ε ∈ (0, 1)` depending only on `ε` such that the
ellipsoid of shape [1, Eq. 16] at `γ = 1/√(n(1+ε))` has volume at most `κ_ε` times that of the
unit ball: `κ_ε = exp(1/√(1+ε) + ε/(2(1+ε)) − 1)`. The volume of an ellipsoid is
`V_n √det` of its shape, so the ratio is `√det E`, which `cutShape_det_le` bounds by `κ_ε`; and
`κ_ε < 1` since the exponent is `−(u − 1)²/(2u²)` for `u = √(1+ε) > 1`. The lemma needs `n ≥ 2`.

## Inputs
* `ε` – approximation tolerance

## Hypotheses
* `hε` – `0 < ε`

## Conclusion
* the cut ellipsoid has at most `κ` times the ball's volume for some `κ < 1`

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4.4]: `vol(E) ≤ κ_ε vol(B)`, `κ_ε ∈ (0, 1)` depending only on `ε`. -/
theorem Ellipsoid.cut_volume_le {ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ (n : ℕ) (c : Vec ℝ n), 2 ≤ n → c ⬝ᵥ c = 1 →
      (Ellipsoid.ofShape (Ellipsoid.cutShape n c (1 / Real.sqrt ((n : ℝ) * (1 + ε)))) 0).volume
        ≤ ENNReal.ofReal κ * (Ellipsoid.ofShape (1 : Mat ℝ n n) 0).volume := by -- --- PROOF ---
  have hε1 : 0 < 1 + ε := by linarith
  have hu : 1 < Real.sqrt (1 + ε) := by
    rw [Real.lt_sqrt zero_le_one]; linarith
  refine ⟨Real.exp (1 / Real.sqrt (1 + ε) - 1 + ε / (2 * (1 + ε))), Real.exp_pos _, ?_, ?_⟩
  · -- the exponent is negative: `1/u + (u² − 1)/(2u²) < 1` for `u = √(1+ε) > 1`
    rw [Real.exp_lt_one_iff]
    have hsq : Real.sqrt (1 + ε) ^ 2 = 1 + ε := Real.sq_sqrt hε1.le
    set u := Real.sqrt (1 + ε) with hu'
    have hε' : ε = u ^ 2 - 1 := by linarith
    rw [hε', show 1 + (u ^ 2 - 1) = u ^ 2 by ring]
    have hu0 : 0 < u := by linarith
    rw [show 1 / u - 1 + (u ^ 2 - 1) / (2 * u ^ 2) = -(u - 1) ^ 2 / (2 * u ^ 2) by
      field_simp; ring]
    exact div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos (sub_pos.2 hu)]) (by positivity)
  · intro n c hn hc
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by linarith
    set γ := 1 / Real.sqrt ((n : ℝ) * (1 + ε)) with hγ
    have hγ0 : 0 < γ := by positivity
    have hγ2 : (n : ℝ) * γ ^ 2 = 1 / (1 + ε) := by
      rw [hγ, div_pow, Real.sq_sqrt (by positivity)]; field_simp
    have hγn : (n : ℝ) * γ ^ 2 < 1 := by
      rw [hγ2, div_lt_one hε1]; linarith
    have hQ := Ellipsoid.cutShape_posDef hc hn hγ0 hγn
    -- the volumes are `V_n √det` of the shapes, and the root of the determinant is below `κ`
    simp only [Ellipsoid.volume]
    rw [Ellipsoid.ofShape_eq hQ.posSemidef, Ellipsoid.ofShape_eq Matrix.PosSemidef.one,
      det_one, Real.sqrt_one, mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hV : 0 ≤ Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
      have : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
      positivity
    rw [mul_comm (Real.exp _)]
    refine mul_le_mul_of_nonneg_left ?_ hV
    -- `√det ≤ κ` from `det ≤ κ²`
    have hdet := Ellipsoid.cutShape_det_le hc hn hε
    calc Real.sqrt (Ellipsoid.cutShape n c γ).det
        ≤ Real.sqrt (Real.exp (1 / Real.sqrt (1 + ε) - 1 + ε / (2 * (1 + ε))) ^ 2) := by
          refine Real.sqrt_le_sqrt (hdet.trans (le_of_eq ?_))
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
      _ = Real.exp (1 / Real.sqrt (1 + ε) - 1 + ε / (2 * (1 + ε))) :=
          Real.sqrt_sq (Real.exp_pos _).le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
