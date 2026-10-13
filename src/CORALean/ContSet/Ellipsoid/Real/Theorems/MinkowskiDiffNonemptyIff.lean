module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# When the Minkowski difference of two ellipsoids is nonempty

[1, Sec. II (Minkowski difference)]: `E(q₁, Q₁) -̇ E(q₂, Q₂) = {x | x + E(q₂, Q₂) ⊆ E(q₁, Q₁)}` is
nonempty iff `E(0, Q₂) ⊆ E(0, Q₁)`. If a translate of the second shape fits in the first, so does
its reflection, both being centrally symmetric, and the midpoint of the two is the shape itself.

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.minkowskiDiff_nonempty_iff (E₁ E₂ : Ellipsoid n) :
    (minkowskiDiff E₁.construct E₂.construct).Nonempty ↔
      (⟨E₂.k, 0, E₂.G⟩ : Ellipsoid n).construct ⊆
        (⟨E₁.k, 0, E₁.G⟩ : Ellipsoid n).construct := by -- --- PROOF ---
  constructor
  · rintro ⟨x, hx⟩ _ ⟨u, hu, rfl⟩
    -- `c ± G₂ u` both lie in the centred first ellipsoid, `c = x + q₂ - q₁`
    have hin : ∀ u' : Vec ℝ E₂.k, ‖u'‖₂ ≤ 1 →
        (x + E₂.q - E₁.q) + E₂.G *ᵥ u' ∈ (⟨E₁.k, 0, E₁.G⟩ : Ellipsoid n).construct := by
      intro u' hu'
      obtain ⟨w, hw, heq⟩ := hx _ ⟨u', hu', rfl⟩
      exact ⟨w, hw, by rw [zero_add, ← sub_eq_iff_eq_add'.mpr heq]; abel⟩
    have hp := hin u hu
    have hm := hin (-u) (by rw [show -u = (-1 : ℝ) • u by simp, norm₂_smul]; simpa using hu)
    -- reflect the second point through the centre
    obtain ⟨w, hw, hweq⟩ := hm
    have hm' : -(x + E₂.q - E₁.q) + E₂.G *ᵥ u ∈ (⟨E₁.k, 0, E₁.G⟩ : Ellipsoid n).construct :=
      ⟨-w, by rw [show -w = (-1 : ℝ) • w by simp, norm₂_smul]; simpa using hw, by
        rw [Matrix.mulVec_neg, zero_add]
        have : E₁.G *ᵥ w = (x + E₂.q - E₁.q) + E₂.G *ᵥ -u := by rw [hweq, zero_add]
        rw [this, Matrix.mulVec_neg]
        abel⟩
    have hmid := (Ellipsoid.convex_construct _) hp hm' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    -- the midpoint of `c + G₂ u` and `-c + G₂ u` is `G₂ u`
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
