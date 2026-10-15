module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Every face of a zonotope is centrally symmetric

The half of [1, Prop. 1] that is about zonotopes rather than about the
counterexample: what [1] appeals to when it reads off Fig. 6 that "not all
faces are centrally symmetric as it has to be for zonotopes".

A direction `u` bounded by `t` on the zonotope cuts out the face `u y = t`.
Every coefficient of a point on it is already extreme wherever `u` does not
annihilate its generator, so only the annihilated generators are still free —
the face is the zonotope on those, and is symmetric about its own center
`c + ∑ sgn(u g⁽ᵘ⁾) g⁽ᵘ⁾`. No hypothesis says `t` is attained: above the
maximum the face is empty and the statement is vacuous.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The face a bounding direction cuts out of a zonotope is symmetric about a
point of its own. -/
theorem Zonotope.face_centrally_symmetric (Z : Zonotope α) (u : α →ₗ[ℝ] ℝ) (t : ℝ)
    (ht : ∀ x ∈ Z.construct, u x ≤ t) :
    ∃ m : α, ∀ x ∈ Z.construct, u x = t →
      (2 : ℝ) • m - x ∈ Z.construct ∧ u ((2 : ℝ) • m - x) = t := by -- --- PROOF ---
  classical
  set σ : Fin Z.h → ℝ :=
    fun υ => if 0 < u (Z.G υ) then 1 else if u (Z.G υ) < 0 then -1 else 0 with hσdef
  have hσ : ∀ υ, σ υ * u (Z.G υ) = |u (Z.G υ)| := by
    intro υ
    rcases lt_trichotomy (u (Z.G υ)) 0 with h | h | h
    · rw [hσdef]; simp [asymm h, h, abs_of_neg h]
    · rw [hσdef]; simp [h]
    · rw [hσdef]; simp [h, abs_of_pos h]
  refine ⟨Z.c + ∑ υ, σ υ • Z.G υ, ?_⟩
  intro x hx hux
  obtain ⟨β, hβ, rfl⟩ := hx
  -- the zonotope's own farthest point in the direction `u`, which `t` bounds
  have hfar : u Z.c + ∑ υ, |u (Z.G υ)| ≤ t := by
    have hmem : Z.c + ∑ υ, σ υ • Z.G υ ∈ Z.construct := by
      refine ⟨σ, fun υ => ?_, rfl⟩
      rcases lt_trichotomy (u (Z.G υ)) 0 with h | h | h
      · rw [hσdef]; simp [asymm h, h]
      · rw [hσdef]; simp [h]
      · rw [hσdef]; simp [h]
    have := ht _ hmem
    rw [map_add, map_sum] at this
    simp only [map_smul, smul_eq_mul, hσ] at this
    exact this
  -- what the point on the face contributes, coefficient by coefficient
  have hxu : u Z.c + ∑ υ, β υ * u (Z.G υ) = t := by
    rw [map_add, map_sum] at hux
    simpa only [map_smul, smul_eq_mul] using hux
  have hle : ∑ υ, β υ * u (Z.G υ) ≤ ∑ υ, |u (Z.G υ)| :=
    Finset.sum_le_sum fun υ _ => by
      calc β υ * u (Z.G υ) ≤ |β υ * u (Z.G υ)| := le_abs_self _
        _ = |β υ| * |u (Z.G υ)| := abs_mul _ _
        _ ≤ 1 * |u (Z.G υ)| := mul_le_mul_of_nonneg_right (hβ υ) (abs_nonneg _)
        _ = |u (Z.G υ)| := one_mul _
  -- so no coefficient can fall short: every term of the sum is already extreme
  have hterm : ∀ υ, β υ * u (Z.G υ) = |u (Z.G υ)| := by
    have hnn : ∀ υ ∈ Finset.univ, 0 ≤ |u (Z.G υ)| - β υ * u (Z.G υ) := by
      intro υ _
      have : β υ * u (Z.G υ) ≤ |u (Z.G υ)| := by
        calc β υ * u (Z.G υ) ≤ |β υ * u (Z.G υ)| := le_abs_self _
          _ = |β υ| * |u (Z.G υ)| := abs_mul _ _
          _ ≤ 1 * |u (Z.G υ)| := mul_le_mul_of_nonneg_right (hβ υ) (abs_nonneg _)
          _ = |u (Z.G υ)| := one_mul _
      linarith
    have hsum : ∑ υ, (|u (Z.G υ)| - β υ * u (Z.G υ)) = 0 := by
      rw [Finset.sum_sub_distrib]
      linarith
    -- a sum of nonnegative terms that vanishes has every term zero
    intro υ
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum υ (Finset.mem_univ υ)
    linarith
  -- every free coefficient flips, every pinned one is already `σ`
  have hrw : (2 : ℝ) • (Z.c + ∑ υ, σ υ • Z.G υ) - (Z.c + ∑ υ, β υ • Z.G υ)
      = Z.c + ∑ υ, ((2 : ℝ) * σ υ - β υ) • Z.G υ := by
    have hpt : ∀ υ, ((2 : ℝ) * σ υ - β υ) • Z.G υ
        = (2 : ℝ) • (σ υ • Z.G υ) - β υ • Z.G υ := fun υ => by rw [sub_smul, smul_smul]
    rw [Finset.sum_congr rfl fun υ _ => hpt υ, Finset.sum_sub_distrib, ← Finset.smul_sum]
    module
  -- the reflected coefficients stay bounded: `-β` where `u` annihilates, `σ` elsewhere
  have hcoef : ∀ υ, |(2 : ℝ) * σ υ - β υ| ≤ 1 := by
    intro υ
    rcases lt_trichotomy (u (Z.G υ)) 0 with h | h | h
    · have hb : β υ = -1 := by
        have h1 : (β υ + 1) * u (Z.G υ) = 0 := by
          have h2 := hterm υ
          rw [abs_of_neg h] at h2
          linear_combination h2
        rcases mul_eq_zero.mp h1 with h2 | h2
        · linarith
        · exact absurd h2 (ne_of_lt h)
      rw [hσdef]
      simp only [if_neg (asymm h), if_pos h, hb]
      norm_num
    · rw [hσdef]
      simp only [h, lt_irrefl, if_neg, not_false_iff, mul_zero, zero_sub, abs_neg]
      simpa using hβ υ
    · -- the last case, `u` positive on the generator, pins `β υ` to `1`
      have hb : β υ = 1 := by
        have h1 : (β υ - 1) * u (Z.G υ) = 0 := by
          have h2 := hterm υ
          rw [abs_of_pos h] at h2
          linear_combination h2
        rcases mul_eq_zero.mp h1 with h2 | h2
        · linarith
        · exact absurd h2 (ne_of_gt h)
      rw [hσdef]
      simp only [if_pos h, hb]
      norm_num
  -- the reflection lands back in the zonotope, and on the same face
  refine ⟨?_, ?_⟩
  · rw [hrw]
    exact ⟨fun υ => (2 : ℝ) * σ υ - β υ, hcoef, rfl⟩
  · rw [hrw, map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    have hpt2 : ∀ υ, ((2 : ℝ) * σ υ - β υ) * u (Z.G υ) = β υ * u (Z.G υ) :=
      fun υ => by linear_combination 2 * hσ υ - 2 * hterm υ
    rw [Finset.sum_congr rfl fun υ _ => hpt2 υ]
    exact hxu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
