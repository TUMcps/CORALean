module

public import CORALean.NN.Layers.Definitions.DeepZRelu
public import CORALean.NN.Layers.Definitions.Relu
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# DeepZ's ReLU band has the least area

[1, Thm. 3.1], the optimality half, over the parallelograms of [1, Fig. 1] at every slope: a band `λ
t + c ≤ ReLU(t) ≤ λ t + d` over a crossing box `[l, u]` has area `(d - c)(u - l)` in the
input-output plane, and no sound band has less than DeepZ's, `2 μ (u - l) = -l u`. At `t = 0` the
band gives `c ≤ 0`, and at the two ends `d ≥ -λ l` and `d ≥ (1 - λ) u`; [1, Eq. 3] and [1, Eq. 4]
are the two families' areas, minimized where they meet. The paper's class `O` of zonotopes is wider
than these bands and not defined beyond the figure.

## Inputs
* `l` – lower end of the box
* `u` – upper end of the box
* `lam` – slope of the band
* `c` – lower offset of the band
* `d` – upper offset of the band

## Hypotheses
* `hl` – box starts below zero
* `hu` – box ends above zero
* `hband` – the band encloses ReLU on the box

## Conclusion
* the band's area is at least DeepZ's

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every sound band over a crossing box is at least as large as DeepZ's. -/
theorem relu_band_area_le {l u lam c d : ℝ} (hl : l < 0) (hu : 0 < u)
    (hband : ∀ t, l ≤ t → t ≤ u → lam * t + c ≤ relu t ∧ relu t ≤ lam * t + d) :
    (deepZRelu.error l u + deepZRelu.error l u) * (u - l)
      ≤ (d - c) * (u - l) := by -- --- PROOF ---
  have herr : deepZRelu.error l u = -(u * l) / (2 * (u - l)) := by
    simp [deepZRelu, not_lt.mpr hl.le, not_le.mpr hu]
  have hw : u - l ≠ 0 := by linarith
  have harea : (deepZRelu.error l u + deepZRelu.error l u) * (u - l) = -(l * u) := by
    rw [herr]; field_simp; ring
  rw [harea]
  -- the band read at `0` and at both ends
  have h0 := (hband 0 hl.le hu.le).1
  have hlo := (hband l le_rfl (by linarith)).2
  have hhi := (hband u (by linarith) le_rfl).2
  simp only [relu, max_eq_right hl.le, max_eq_left hu.le, max_self, mul_zero, zero_add]
    at h0 hlo hhi
  nlinarith [mul_nonneg hu.le (show 0 ≤ lam * l + d by linarith),
    mul_nonneg (neg_nonneg.mpr hl.le) (show 0 ≤ lam * u + d - u by linarith),
    mul_nonneg (show (0:ℝ) ≤ u - l by linarith) (neg_nonneg.mpr h0)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
