module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestDot
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# The distance from an ellipsoid to a hyperplane

[1, Sec. II (distances)]: `dist(E(q, Q), H(v, c)) = (|c - ⟨v, q⟩| - ⟨v, Q v⟩^{1/2}) / ⟨v, v⟩^{1/2}`.
On `E` the value `vᵀ x` sweeps the whole interval `[vᵀ q - σ, vᵀ q + σ]`, `σ = (vᵀ Q v)^{1/2}`,
so `E` meets `H` exactly when `|c - vᵀ q| ≤ σ`; otherwise the gap `|c - vᵀ q| - σ` divided by
`‖v‖₂` is the Euclidean distance, attained at the extreme point of `E` towards `H` and its
projection onto `H`. The paper says the value is negative when `E` and `H` intersect
[1, Sec. II (sign of the distance)], which fails at tangency, where it is `0`.

## Inputs
* `E` – ellipsoid
* `v` – hyperplane normal
* `c` – hyperplane offset

## Hypotheses
* `hv` – `v ≠ 0`

## Conclusion
* the distance to the hyperplane is the closed form, zero if they meet

## References

* [1] [A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". Proceedings of the 45th IEEE
      Conference on Decision and Control,
      2006.](../../../../../../references/2006/kurzhanskiy-cdc-ellipsoidal-toolbox.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.dist_hyperplane_eq (E : Ellipsoid n) (v : Vec ℝ n) (c : ℝ)
    (hv : v ≠ 0) : -- --- CONCL ---
    ((E.construct ∩ {x | v ⬝ᵥ x = c}).Nonempty ↔
        |c - v ⬝ᵥ E.q| - √(v ⬝ᵥ (E.Q *ᵥ v)) ≤ 0) ∧
    (0 < |c - v ⬝ᵥ E.q| - √(v ⬝ᵥ (E.Q *ᵥ v)) →
      IsLeast {t | ∃ x ∈ E.construct, ∃ y : Vec ℝ n, v ⬝ᵥ y = c ∧ t = ‖x - y‖₂}
        ((|c - v ⬝ᵥ E.q| - √(v ⬝ᵥ (E.Q *ᵥ v))) / ‖v‖₂)) := by -- --- PROOF ---
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = v ⬝ᵥ E.q := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = √(v ⬝ᵥ (E.Q *ᵥ v)) := ⟨_, rfl⟩
  rw [← hm, ← hσ]
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact Real.sqrt_nonneg _
  -- the largest value `m + σ` and, along `-v`, the least value `m - σ` of `vᵀ x` on `E`
  obtain ⟨⟨xp, hxp, hxpv⟩, hub⟩ := E.isGreatest_dot v
  obtain ⟨⟨xm, hxm, hxmv⟩, hlb⟩ := E.isGreatest_dot (-v)
  have hsq : (-v) ⬝ᵥ (E.Q *ᵥ -v) = v ⬝ᵥ (E.Q *ᵥ v) := by
    rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [hsq, ← hσ, neg_dotProduct, ← hm] at hxmv hlb
  rw [← hσ, ← hm] at hxpv hub
  simp only [neg_dotProduct] at hxmv hxpv
  have hrange : ∀ x ∈ E.construct, m - σ ≤ v ⬝ᵥ x ∧ v ⬝ᵥ x ≤ m + σ := fun x hx => by
    have h1 := hub ⟨x, hx, rfl⟩
    have h2 := hlb ⟨x, hx, rfl⟩
    simp only [neg_dotProduct] at h1 h2
    exact ⟨by linarith, h1⟩
  have hvpos : 0 < ‖v‖₂ := by
    rcases (norm₂_nonneg v).eq_or_lt with h | h
    · exact absurd (dotProduct_self_eq_zero.mp (by rw [dotProduct_self, ← h]; ring)) hv
    · exact h
  -- a point `x₀` of `E` and its projection onto `H` are `|c - vᵀ x₀| / ‖v‖₂` apart
  have hproj : ∀ x₀ ∈ E.construct, |c - v ⬝ᵥ x₀| / ‖v‖₂ ∈
      {t | ∃ x ∈ E.construct, ∃ y : Vec ℝ n, v ⬝ᵥ y = c ∧ t = ‖x - y‖₂} := fun x₀ hx₀ => by
    refine ⟨x₀, hx₀, x₀ + ((c - v ⬝ᵥ x₀) / ‖v‖₂ ^ 2) • v, ?_, ?_⟩
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_self]
      field_simp
      ring
    · rw [sub_add_cancel_left, show -(((c - v ⬝ᵥ x₀) / ‖v‖₂ ^ 2) • v) =
        (-((c - v ⬝ᵥ x₀) / ‖v‖₂ ^ 2)) • v by rw [neg_smul], norm₂_smul, abs_neg, abs_div,
        abs_of_pos (pow_pos hvpos 2)]
      field_simp
  refine ⟨⟨?_, fun hle => ?_⟩, fun hpos => ⟨?_, ?_⟩⟩
  -- a common point puts `c` in `[m - σ, m + σ]`
  · rintro ⟨x, hx, hxc⟩
    obtain ⟨h1, h2⟩ := hrange x hx
    have hxc' : v ⬝ᵥ x = c := hxc
    rw [sub_nonpos, abs_sub_le_iff]
    constructor <;> linarith
  -- conversely the segment from the least to the largest point crosses `H`
  · obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (sub_nonpos.mp hle)
    rcases hσ0.eq_or_lt with h0 | hσpos
    · refine ⟨xp, hxp, ?_⟩
      show v ⬝ᵥ xp = c
      rw [← h0] at h1 h2
      linarith
    · obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (c - (m - σ)) / (2 * σ) := ⟨_, rfl⟩
      have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith) (by linarith)
      have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
      refine ⟨(1 - θ) • xm + θ • xp,
        E.convex_construct hxm hxp (by linarith) hθ0 (by ring), ?_⟩
      show v ⬝ᵥ ((1 - θ) • xm + θ • xp) = c
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hxm' : v ⬝ᵥ xm = m - σ := by linarith
      rw [hxm', hxpv, hθ]
      field_simp
      ring
  -- attained at the extreme point on the side of `H`
  · rcases le_or_gt 0 (c - m) with hcm | hcm
    · have := hproj xp hxp
      rwa [hxpv, show c - (m + σ) = |c - m| - σ by rw [abs_of_nonneg hcm]; ring,
        abs_of_pos hpos] at this
    · have := hproj xm hxm
      rwa [show v ⬝ᵥ xm = m - σ by linarith, show c - (m - σ) = -(|c - m| - σ) by
        rw [abs_of_neg hcm]; ring, abs_neg, abs_of_pos hpos] at this
  -- every pair: `|c - m| - σ ≤ |vᵀ x - c| = |vᵀ (x - y)| ≤ ‖v‖₂ ‖x - y‖₂`
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := hrange x hx
    have hcs := abs_dotProduct_le_norm₂_mul_norm₂ v (x - y)
    rw [dotProduct_sub, hy] at hcs
    rw [div_le_iff₀ hvpos, mul_comm]
    refine le_trans ?_ hcs
    rcases le_or_gt 0 (c - m) with hcm | hcm
    · rw [abs_of_nonneg hcm]
      exact le_trans (by linarith) (neg_le_abs _)
    · rw [abs_of_neg hcm]
      exact le_trans (by linarith) (le_abs_self _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
