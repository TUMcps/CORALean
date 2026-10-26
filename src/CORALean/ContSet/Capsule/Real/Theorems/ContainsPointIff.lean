module

public import CORALean.ContSet.Capsule.Real.Operations.ContainsPoint
public import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm

@[expose] public section

/-!
# `Capsule.containsPoint` is exact

`p` is in the capsule iff `containsPoint` holds, for every capsule (a negative radius denotes `∅`
and fails both sides; `g = 0` is the sphere, CORA's `isempty(g)` case). With `v = p - c` and
`Q t = ‖v - t g‖₂²`, `Q t = Q s + ‖g‖₂² (t - s)²` at the foot `s` of the projection, so the best
`t ∈ [-1, 1]` is `s` when `|s| < 1` and the nearer end otherwise: CORA's two branches.

## Inputs
* `C` – capsule
* `p` – point

## Hypotheses
* none

## Conclusion
* `containsPoint` is membership
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_sq_sub_smul (v g : Vec ℝ n) (t : ℝ) :
    ‖v - t • g‖₂ ^ 2 = ‖v‖₂ ^ 2 - 2 * t * (v ⬝ᵥ g) + t ^ 2 * ‖g‖₂ ^ 2 := by
  rw [← dotProduct_self, ← dotProduct_self, ← dotProduct_self]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm g v]
  ring

private theorem aux_norm₂_le_iff (x : Vec ℝ n) (r : ℝ) : -- --- CONCL ---
    ‖x‖₂ ≤ r ↔ 0 ≤ r ∧ ‖x‖₂ ^ 2 ≤ r ^ 2 := by -- --- PROOF ---
  constructor
  · exact fun h => ⟨(norm₂_nonneg x).trans h, pow_le_pow_left₀ (norm₂_nonneg x) h 2⟩
  · rintro ⟨hr, h⟩
    by_contra hlt
    replace hlt := not_le.mp hlt
    nlinarith [norm₂_nonneg x]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.containsPoint_iff (C : Capsule n) (p : Vec ℝ n) : -- --- CONCL ---
    C.containsPoint p ↔ p ∈ C.construct := by -- --- PROOF ---
  rw [Capsule.mem_construct_iff_norm₂]
  simp only [Capsule.containsPoint]
  set v := p - C.c with hv
  by_cases hg : ‖C.g‖₂ = 0
  · -- no direction: the sphere
    have g0 : C.g = 0 := by
      funext i
      have := abs_le_norm₂ C.g i
      rw [hg] at this
      simpa using this
    have hp : p - C.c = v := rfl
    simp only [g0, norm₂_zero, inv_zero, dotProduct_zero, abs_zero, lt_self_iff_false,
      false_and, false_or, not_false_eq_true, true_and, add_zero, sub_zero, or_self, smul_zero]
    constructor
    · exact fun h => ⟨0, ⟨by norm_num, by norm_num⟩, by simpa using h⟩
    · rintro ⟨t, -, ht⟩; simpa using ht
  -- a direction: `s` is the foot of `p` on the axis, in units of `g`
  have hng : 0 < ‖C.g‖₂ := lt_of_le_of_ne (norm₂_nonneg _) (Ne.symm hg)
  set ng := ‖C.g‖₂ with hng_def
  -- the foot of the projection, `b = ng² s`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, v ⬝ᵥ C.g = ng ^ 2 * s := ⟨(v ⬝ᵥ C.g) / ng ^ 2, by field_simp⟩
  have hQ : ∀ t : ℝ, ‖v - t • C.g‖₂ ^ 2 = ‖v - s • C.g‖₂ ^ 2 + ng ^ 2 * (t - s) ^ 2 := by
    intro t
    rw [aux_sq_sub_smul, aux_sq_sub_smul, hs]
    ring
  -- CORA's `proj` and the foot point it computes
  have hproj : v ⬝ᵥ (ng⁻¹ • C.g) = ng * s := by
    rw [dotProduct_smul, smul_eq_mul, hs]; field_simp
  have hpt : (ng * s) • (ng⁻¹ • C.g) = s • C.g := by
    rw [smul_smul]; congr 1; field_simp
  have habs : |ng * s| < ng ↔ |s| < 1 := by
    rw [abs_mul, abs_of_pos hng]
    exact mul_lt_iff_lt_one_right hng
  -- the three distances CORA computes, as offsets `v - t g`
  have hneg : ‖(C.c + s • C.g) - p‖₂ = ‖v - s • C.g‖₂ := by
    have h := norm₂_smul (-1) (v - s • C.g)
    rw [neg_smul, one_smul, abs_neg, abs_one, one_mul] at h
    rw [← h]; congr 1; simp [hv]; abel
  have hp1 : ‖p - (C.c + C.g)‖₂ = ‖v - (1 : ℝ) • C.g‖₂ := by
    congr 1; simp [hv]; abel
  have hp2 : ‖p - (C.c - C.g)‖₂ = ‖v - (-1 : ℝ) • C.g‖₂ := by
    congr 1; simp [hv]; abel
  simp only [hproj, hpt, habs, hneg, hp1, hp2]
  -- the foot lies on the segment: the best point is the foot
  have hd : 0 < ng ^ 2 := by positivity
  by_cases hs1 : |s| < 1
  · simp only [hs1, true_and, not_true_eq_false, false_and, or_false]
    obtain ⟨hs_l, hs_u⟩ := abs_lt.mp hs1
    constructor
    · exact fun h => ⟨s, ⟨hs_l.le, hs_u.le⟩, h⟩
    · rintro ⟨t, -, ht⟩
      rw [aux_norm₂_le_iff] at ht ⊢
      refine ⟨ht.1, ?_⟩
      have := hQ t
      nlinarith [sq_nonneg (t - s)]
  · -- the foot lies off the segment: the best point is the nearer end
    simp only [hs1, false_and, false_or, not_false_eq_true, true_and]
    rw [not_lt, le_abs'] at hs1
    -- an end is a point of the segment; conversely the nearer end beats every `t`
    constructor
    · rintro (h | h)
      · exact ⟨1, ⟨by norm_num, le_rfl⟩, h⟩
      · exact ⟨-1, ⟨le_rfl, by norm_num⟩, h⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, ht⟩
      -- `s ≤ -1`: the end `-1` is nearer than `t`; `1 ≤ s`: the end `1` is
      rw [aux_norm₂_le_iff] at ht
      rcases hs1 with hs1 | hs1
      · right
        rw [aux_norm₂_le_iff]
        refine ⟨ht.1, ?_⟩
        have h1 := hQ t
        have h2 := hQ (-1)
        have : 0 ≤ ng ^ 2 * ((t + 1) * (t - 1 - 2 * s)) :=
          mul_nonneg hd.le (mul_nonneg (by linarith) (by linarith))
        linarith [ht.2]
      · left
        rw [aux_norm₂_le_iff]
        refine ⟨ht.1, ?_⟩
        have h1 := hQ t
        have h2 := hQ 1
        have : 0 ≤ ng ^ 2 * ((t - 1) * (t + 1 - 2 * s)) :=
          mul_nonneg hd.le (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
        linarith [ht.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
