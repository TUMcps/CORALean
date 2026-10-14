module

public import CORALean.ContSet.InflatedContSet.InflatedContSet

@[expose] public section

/-!
# Composing a nominal part with its box along a segment

The `linComb` counterpart of `plus_subset`:
`λ(n₁+e₁) + (1-λ)(n₂+e₂)` regroups as `(λn₁ + (1-λ)n₂) + (λe₁ + (1-λ)e₂)`, so
the nominal part may spill by `D` and the box must absorb `D` along with the
segment between the two incoming boxes.

Not an instance of `plus_subset`: one weight is shared by both halves.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S₁ S₂ T N₁ N₂ N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N₁ (Vec ℝ n)] [ContSet N₂ (Vec ℝ n)] [ContSet N (Vec ℝ n)]
variable [InflatedContSet S₁ N₁ (Vec 𝕋 n) (Vec ℝ n)]
  [InflatedContSet S₂ N₂ (Vec 𝕋 n) (Vec ℝ n)]
  [InflatedContSet T N (Vec 𝕋 n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem linComb_subset {s₁ : S₁} {s₂ : S₂} {t : T} {D : Set (Vec ℝ n)}
    (hnominal : segments (nominalSet s₁) (nominalSet s₂) ⊆ nominalSet t + D)
    (herror : segments (I_error s₁).construct (I_error s₂).construct + D ⊆
      (I_error t).construct) :
    segments (construct s₁) (construct s₂) ⊆ construct t := by -- --- PROOF ---
  rintro _ ⟨_, ⟨n₁, hn₁, e₁, he₁, rfl⟩, _, ⟨n₂, hn₂, e₂, he₂, rfl⟩, lam, hlam, rfl⟩
  obtain ⟨t₀, ht₀, d, hd, hsum⟩ := hnominal ⟨n₁, hn₁, n₂, hn₂, lam, hlam, rfl⟩
  refine ⟨t₀, ht₀, lam • e₁ + (1 - lam) • e₂ + d,
    herror ⟨_, ⟨e₁, he₁, e₂, he₂, lam, hlam, rfl⟩, d, hd, rfl⟩, ?_⟩
  -- `Set.image2` leaves both sums as beta-redexes, which `rw` will not match
  have hsum' : t₀ + d = lam • n₁ + (1 - lam) • n₂ := hsum
  show t₀ + (lam • e₁ + (1 - lam) • e₂ + d) = lam • (n₁ + e₁) + (1 - lam) • (n₂ + e₂)
  have regroup : t₀ + (lam • e₁ + (1 - lam) • e₂ + d)
      = t₀ + d + (lam • e₁ + (1 - lam) • e₂) := by abel
  rw [regroup, hsum', smul_add, smul_add]
  abel

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
