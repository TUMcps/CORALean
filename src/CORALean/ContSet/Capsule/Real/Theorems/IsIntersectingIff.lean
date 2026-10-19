module

public import CORALean.ContSet.Capsule.Real.Operations.IsIntersecting
public import CORALean.ContSet.Capsule.Real.Theorems.SegDistMem
public import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm

@[expose] public section

/-!
# `Capsule.isIntersecting_` is exact

For capsules with non-negative radii, the axes are within `r₁ + r₂` iff the capsules share a
point: a point of both lies within `r₁` and `r₂` of two axis points, so the triangle inequality
bounds their distance, and conversely the point at the fraction `r₁ / (r₁ + r₂)` of the way
between the two nearest axis points lies in both.

## Inputs
* `C₁` – first capsule
* `C₂` – second capsule

## Hypotheses
* `h₁` – `C₁` nonnegative radius
* `h₂` – `C₂` nonnegative radius

## Conclusion
* `isIntersecting_` is a nonempty intersection
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isIntersecting_iff {C₁ C₂ : Capsule n} (h₁ : 0 ≤ C₁.r) (h₂ : 0 ≤ C₂.r) :
    C₁.isIntersecting_ C₂ ↔ (C₁.construct ∩ C₂.construct).Nonempty := by -- --- PROOF ---
  constructor
  · -- the nearest axis points `A`, `B` and the point a fraction `θ` of the way from `A` to `B`
    intro h
    obtain ⟨t₁, ht₁, t₂, ht₂, hD⟩ := Capsule.segDist_mem C₁ C₂
    set A := C₁.c + t₁ • C₁.g with hA
    set B := C₂.c + t₂ • C₂.g with hB
    have hAB : ‖A - B‖₂ ≤ C₁.r + C₂.r := hD ▸ h
    -- a point of both balls, `A + θ (B - A)`
    have key : ∀ θ : ℝ, ‖(A + θ • (B - A)) - A‖₂ = |θ| * ‖A - B‖₂ ∧
        ‖(A + θ • (B - A)) - B‖₂ = |1 - θ| * ‖A - B‖₂ := by
      intro θ
      constructor
      · have : (A + θ • (B - A)) - A = (-θ) • (A - B) := by
          rw [neg_smul, ← smul_neg, neg_sub]; abel
        rw [this, norm₂_smul, abs_neg]
      · have : (A + θ • (B - A)) - B = (1 - θ) • (A - B) := by
          rw [sub_smul, one_smul, smul_sub, smul_sub]; abel
        rw [this, norm₂_smul]
    -- both radii zero: the axes meet, and `A` is the point
    by_cases hz : C₁.r + C₂.r = 0
    · have hr₁ : C₁.r = 0 := by linarith
      have hr₂ : C₂.r = 0 := by linarith
      have hAB0 : ‖A - B‖₂ = 0 := le_antisymm (by linarith) (norm₂_nonneg _)
      refine ⟨A, ?_, ?_⟩
      · rw [Capsule.mem_construct_iff_norm₂]
        refine ⟨t₁, ht₁, ?_⟩
        have : (A - C₁.c) - t₁ • C₁.g = 0 := by rw [hA]; abel
        rw [this, norm₂_zero, hr₁]
      · rw [Capsule.mem_construct_iff_norm₂]
        refine ⟨t₂, ht₂, ?_⟩
        have : (A - C₂.c) - t₂ • C₂.g = A - B := by rw [hB]; abel
        rw [this, hAB0, hr₂]
    · -- a positive total radius, so `θ` is defined
      have hpos : 0 < C₁.r + C₂.r := lt_of_le_of_ne (by linarith) (Ne.symm hz)
      set θ := C₁.r / (C₁.r + C₂.r) with hθ
      have hθ0 : 0 ≤ θ := div_nonneg h₁ hpos.le
      have hθ1 : θ ≤ 1 := (div_le_one hpos).mpr (by linarith)
      obtain ⟨k1, k2⟩ := key θ
      -- `A + θ (B - A)` is within `r₁` of `A` and within `r₂` of `B`
      refine ⟨A + θ • (B - A), ?_, ?_⟩
      · rw [Capsule.mem_construct_iff_norm₂]
        refine ⟨t₁, ht₁, ?_⟩
        have : ((A + θ • (B - A)) - C₁.c) - t₁ • C₁.g = (A + θ • (B - A)) - A := by
          rw [hA]; abel
        rw [this, k1, abs_of_nonneg hθ0]
        calc θ * ‖A - B‖₂ ≤ θ * (C₁.r + C₂.r) := mul_le_mul_of_nonneg_left hAB hθ0
          _ = C₁.r := by rw [hθ]; field_simp
      · rw [Capsule.mem_construct_iff_norm₂]
        refine ⟨t₂, ht₂, ?_⟩
        have : ((A + θ • (B - A)) - C₂.c) - t₂ • C₂.g = (A + θ • (B - A)) - B := by
          rw [hB]; abel
        rw [this, k2, abs_of_nonneg (by linarith)]
        calc (1 - θ) * ‖A - B‖₂ ≤ (1 - θ) * (C₁.r + C₂.r) :=
              mul_le_mul_of_nonneg_left hAB (by linarith)
          _ = C₂.r := by rw [hθ]; field_simp; ring
  · -- a common point `x`: the triangle inequality through it bounds the axis distance
    rintro ⟨x, hx₁, hx₂⟩
    rw [Capsule.mem_construct_iff_norm₂] at hx₁ hx₂
    obtain ⟨t₁, ht₁, hx₁⟩ := hx₁
    obtain ⟨t₂, ht₂, hx₂⟩ := hx₂
    have hle : Capsule.segDist C₁ C₂ ≤ ‖(C₁.c + t₁ • C₁.g) - (C₂.c + t₂ • C₂.g)‖₂ :=
      csInf_le ⟨0, by rintro _ ⟨t, -, rfl⟩; exact norm₂_nonneg _⟩
        ⟨(t₁, t₂), ⟨ht₁, ht₂⟩, rfl⟩
    have e : (C₁.c + t₁ • C₁.g) - (C₂.c + t₂ • C₂.g)
        = -((x - C₁.c) - t₁ • C₁.g) + ((x - C₂.c) - t₂ • C₂.g) := by abel
    have h3 := norm₂_add_le (-((x - C₁.c) - t₁ • C₁.g)) ((x - C₂.c) - t₂ • C₂.g)
    have h4 : ‖-((x - C₁.c) - t₁ • C₁.g)‖₂ = ‖(x - C₁.c) - t₁ • C₁.g‖₂ := by
      have h := norm₂_smul (-1) ((x - C₁.c) - t₁ • C₁.g)
      rw [neg_smul, one_smul, abs_neg, abs_one, one_mul] at h
      exact h
    rw [← e] at h3
    unfold Capsule.isIntersecting_
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
