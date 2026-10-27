module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripGollamudi1D

@[expose] public section

/-!
# CORA's `intersectStrip` (Gollamudi) does not enclose the intersection

The ellipsoid `[-1, 1]` (`Q = 1`, `c = 0`) and the strip `|x - 2| ≤ 3`, that is `[-1, 5]`,
which contains it: the intersection is `[-1, 1]`. CORA's update, at any weight `λ ∈ (0, 1)`
(the code takes `min(1e-4, ν)`), returns the ellipsoid with center `2λ` and shape
`1 / (1 + 2λ)²`, which misses `x = -1`: `(-1 - 2λ)² / Q' = (1 + 2λ)⁴ > 1`. The shape
is divided by `σ² = 1 + 4λ + 4λ² > 1` where the enclosure needs `σ² Q'`: from
`(1 - λ)(x - c)ᵀ Q⁻¹ (x - c) + λ |C x - y|² ≤ 1 - λ + λ φ²` one gets
`(x - c*)ᵀ Q'⁻¹ (x - c*) ≤ σ²`.

## Inputs
* `lam` – update weight

## Hypotheses
* `h0` – `0 < lam`
* `h1` – `lam < 1`

## Conclusion
* a point of the intersection falls outside the computed ellipsoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.intersectStripGollamudi1D_counterexample (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam < 1) : -- --- CONCL ---
    let E' := Ellipsoid.intersectStripGollamudi1D 1 0 1 3 2 lam
    (-1 : ℝ) ^ 2 / 1 ≤ 1 ∧ |(-1 : ℝ) - 2| ≤ 3 ∧ 1 < (-1 - E'.1) ^ 2 / E'.2 := by -- --- PROOF ---
  intro E'
  refine ⟨by norm_num, by norm_num [abs_of_neg], ?_⟩
  -- the update in closed form: center `2 lam`, shape `1 / (1 + 2 lam)^2`
  have hc : E'.1 = 2 * lam := by
    simp [E', Ellipsoid.intersectStripGollamudi1D, mul_comm]
  have hq : E'.2 = ((1 + 2 * lam) ^ 2)⁻¹ := by
    simp only [E', Ellipsoid.intersectStripGollamudi1D]
    have h : (1 - lam) * (1 : ℝ)⁻¹ + lam * (1 * 1) = 1 := by ring
    have h2 : (1 - lam) + lam * (1 * 1 * 1) = (1 : ℝ) := by ring
    rw [h, h2]
    ring
  rw [hc, hq]
  -- `(1 + 2 lam)^4 > 1`
  have hp : 0 < 1 + 2 * lam := by linarith
  rw [div_inv_eq_mul]
  have : (-1 - 2 * lam) ^ 2 * (1 + 2 * lam) ^ 2 = ((1 + 2 * lam) ^ 2) ^ 2 := by ring
  rw [this]
  have h3 : 1 < (1 + 2 * lam) ^ 2 := by nlinarith
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
