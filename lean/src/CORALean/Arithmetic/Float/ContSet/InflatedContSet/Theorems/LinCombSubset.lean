import CORALean.Arithmetic.Float.ContSet.InflatedContSet.InflatedContSet

/-!
# Composing a nominal part with its box along a segment

The `linComb` counterpart of `plus_subset`. A segment between two inflated sets
splits into a segment between the nominal parts and a segment between the boxes,
because both weights act on the sum at once: `λ(n₁+e₁) + (1-λ)(n₂+e₂)` regroups
as `(λn₁ + (1-λ)n₂) + (λe₁ + (1-λ)e₂)`.

So the nominal part may spill by `D`, and the box must absorb `D` along with the
segment between the two incoming boxes — one weight, shared by both halves,
which is why this is not an instance of `plus_subset`.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.InflatedContSet

open Pointwise

variable {𝕋 S₁ S₂ T N₁ N₂ N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [Real.ContSet N₁ n] [Real.ContSet N₂ n] [Real.ContSet N n]
variable [InflatedContSet S₁ N₁ 𝕋 n] [InflatedContSet S₂ N₂ 𝕋 n] [InflatedContSet T N 𝕋 n]

theorem linComb_subset {s₁ : S₁} {s₂ : S₂} {t : T} {D : Set (Vec ℝ n)}
    (hnominal : Real.segments (nominalSet s₁) (nominalSet s₂) ⊆ nominalSet t + D)
    (herror : Real.segments (error s₁).construct (error s₂).construct + D ⊆
      (error t).construct) :
    Real.segments (construct s₁) (construct s₂) ⊆ construct t := by
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

end CORALean.Arithmetic.Float.InflatedContSet
