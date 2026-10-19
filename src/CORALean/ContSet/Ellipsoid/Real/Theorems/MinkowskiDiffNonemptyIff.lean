module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# When the Minkowski difference of two ellipsoids is nonempty

[1, Sec. II (Minkowski difference)]: `E(q₁, Q₁) -̇ E(q₂, Q₂) = {x | x + E(q₂, Q₂) ⊆ E(q₁, Q₁)}` is
nonempty iff `E(0, Q₂) ⊆ E(0, Q₁)`. If a translate of the second shape fits in the first, so does
its reflection, both being centrally symmetric, and the midpoint of the two is the shape itself.

## Inputs
* `E₁` – minuend
* `E₂` – subtrahend

## Hypotheses
* none

## Conclusion
* the difference is nonempty iff `E₂` fits into `E₁` centered at the origin

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.minkowskiDiff_nonempty_iff (E₁ E₂ : Ellipsoid n) :
    (minkowskiDiff E₁.construct E₂.construct).Nonempty ↔
      (⟨E₂.Q, 0, E₂.psd⟩ : Ellipsoid n).construct ⊆
        (⟨E₁.Q, 0, E₁.psd⟩ : Ellipsoid n).construct := by -- --- PROOF ---
  -- the centered ellipsoid has the same generator
  have hc : ∀ E : Ellipsoid n, (⟨E.Q, 0, E.psd⟩ : Ellipsoid n).construct
      = {x | ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧ x = 0 + E.G *ᵥ u} := fun E => Ellipsoid.construct_eq_sqrt _
  rw [hc, hc, E₁.construct_eq_sqrt, E₂.construct_eq_sqrt]
  constructor
  · rintro ⟨x, hx⟩ _ ⟨u, hu, rfl⟩
    -- `c ± G₂ u` both lie in the centered first ellipsoid, `c = x + q₂ - q₁`
    have hin : ∀ u' : Vec ℝ n, ‖u'‖₂ ≤ 1 →
        (x + E₂.q - E₁.q) + E₂.G *ᵥ u' ∈ {x | ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧ x = 0 + E₁.G *ᵥ u} := by
      intro u' hu'
      obtain ⟨w, hw, heq⟩ := hx _ ⟨u', hu', rfl⟩
      exact ⟨w, hw, by rw [zero_add, ← sub_eq_iff_eq_add'.mpr heq]; abel⟩
    have hp := hin u hu
    have hm := hin (-u) (by rw [show -u = (-1 : ℝ) • u by simp, norm₂_smul]; simpa using hu)
    -- reflect the second point through the center
    obtain ⟨w, hw, hweq⟩ := hm
    have hm' : -(x + E₂.q - E₁.q) + E₂.G *ᵥ u ∈ {x | ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧ x = 0 + E₁.G *ᵥ u} :=
      ⟨-w, by rw [show -w = (-1 : ℝ) • w by simp, norm₂_smul]; simpa using hw, by
        rw [Matrix.mulVec_neg, zero_add]
        have : E₁.G *ᵥ w = (x + E₂.q - E₁.q) + E₂.G *ᵥ -u := by rw [hweq, zero_add]
        rw [this, Matrix.mulVec_neg]
        abel⟩
    rw [← hc E₁] at hp hm'
    have hmid := (Ellipsoid.convex_construct ⟨E₁.Q, 0, E₁.psd⟩) hp hm'
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    -- the midpoint of `c + G₂ u` and `-c + G₂ u` is `G₂ u`
    rw [hc] at hmid
    convert hmid using 1
    show (0 : Vec ℝ n) + E₂.G *ᵥ u = _
    simp only [smul_add, smul_neg, zero_add]
    module
  -- conversely `q₁ - q₂` is in the difference
  · intro hsub
    refine ⟨E₁.q - E₂.q, fun y ⟨u, hu, hy⟩ => ?_⟩
    obtain ⟨w, hw, heq⟩ := hsub ⟨u, hu, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [hy]
    simp only [zero_add] at heq
    rw [← heq]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
