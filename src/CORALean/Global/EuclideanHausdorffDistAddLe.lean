module

public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# Minkowski sums move apart by at most the sum of the two distances

`d_H(S₁ ⊕ S₂, T₁ ⊕ T₂) ≤ d_H(S₁,T₁) + d_H(S₂,T₂)`, at `‖·‖₂`. The witness for a point `s₁ + s₂` is
the nearest point of `T₁` to `s₁` added to the nearest point of `T₂` to `s₂`, which is why the sets
have to be compact and nonempty, as a paper stating the Hausdorff distance for compact sets already
asks. The one-sided `d_H(S ⊕ V, S ⊕ W) ≤ d_H(V,W)` is `ContSet/ContSet/Theorems`'
`hausdorffDist_add_le`, out of reach from here since `Global` is below `ContSet`, so the argument
is made once more.

## Inputs
* `S₁` – first summand of the first sum
* `S₂` – first summand of the second sum
* `T₁` – second summand of the first sum
* `T₂` – second summand of the second sum

## Hypotheses
* `hS₁` – `S₁` is compact
* `hS₁ne` – `S₁` is nonempty
* `hT₁` – `T₁` is compact
* `hT₁ne` – `T₁` is nonempty
* `hS₂` – `S₂` is compact
* `hS₂ne` – `S₂` is nonempty
* `hT₂` – `T₂` is compact
* `hT₂ne` – `T₂` is nonempty

## Conclusion
* the distance between the sums is at most the sum of the distances of the summands
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One direction of the bound, in any normed group: pair each summand with its own nearest
point. -/
theorem aux_exists_mem_add_add_dist_le {α : Type} [NormedAddCommGroup α] {S₁ S₂ T₁ T₂ : Set α}
    (hT₁ : IsCompact T₁) (hT₁ne : T₁.Nonempty) (hT₂ : IsCompact T₂) (hT₂ne : T₂.Nonempty)
    (hf₁ : Metric.hausdorffEDist S₁ T₁ ≠ ⊤) (hf₂ : Metric.hausdorffEDist S₂ T₂ ≠ ⊤)
    {x : α} (hx : x ∈ S₁ + S₂) : -- --- CONCL ---
    ∃ y ∈ T₁ + T₂, dist x y
      ≤ Metric.hausdorffDist S₁ T₁ + Metric.hausdorffDist S₂ T₂ := by -- --- PROOF ---
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨t₁, ht₁, h₁⟩ := hT₁.exists_infDist_eq_dist hT₁ne s₁
  obtain ⟨t₂, ht₂, h₂⟩ := hT₂.exists_infDist_eq_dist hT₂ne s₂
  refine ⟨t₁ + t₂, Set.add_mem_add ht₁ ht₂, (dist_add_add_le _ _ _ _).trans (add_le_add ?_ ?_)⟩
  · exact h₁ ▸ Metric.infDist_le_hausdorffDist_of_mem hs₁ hf₁
  · exact h₂ ▸ Metric.infDist_le_hausdorffDist_of_mem hs₂ hf₂

/-- `toEuclidean` is additive, so it carries a Minkowski sum to the Minkowski sum of the images. -/
theorem aux_toEuclidean_image_add (X Y : Set (Vec ℝ n)) : -- --- CONCL ---
    toEuclidean '' (X + Y) = toEuclidean '' X + toEuclidean '' Y := by -- --- PROOF ---
  ext z
  constructor
  · rintro ⟨_, hw, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hw
    exact ⟨toEuclidean x, ⟨x, hx, rfl⟩, toEuclidean y, ⟨y, hy, rfl⟩, (map_add _ _ _).symm⟩
  · rintro hz
    obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := Set.mem_add.mp hz
    exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, map_add _ _ _⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `d_H(S₁ ⊕ S₂, T₁ ⊕ T₂) ≤ d_H(S₁,T₁) + d_H(S₂,T₂)`, read at `‖·‖₂`. -/
theorem hausdorffDist₂_add_le {S₁ S₂ T₁ T₂ : Set (Vec ℝ n)}
    (hS₁ : IsCompact S₁) (hS₁ne : S₁.Nonempty) (hT₁ : IsCompact T₁) (hT₁ne : T₁.Nonempty)
    (hS₂ : IsCompact S₂) (hS₂ne : S₂.Nonempty) (hT₂ : IsCompact T₂)
    (hT₂ne : T₂.Nonempty) : -- --- CONCL ---
    hausdorffDist₂ (S₁ + S₂) (T₁ + T₂)
      ≤ hausdorffDist₂ S₁ T₁ + hausdorffDist₂ S₂ T₂ := by -- --- PROOF ---
  have himg : ∀ X : Set (Vec ℝ n), IsCompact X → IsCompact (toEuclidean '' X) :=
    fun _ hX => hX.image toEuclidean.continuous
  have hne : ∀ X : Set (Vec ℝ n), X.Nonempty → (toEuclidean '' X).Nonempty :=
    fun _ hX => hX.image _
  -- both distances are finite, which is what lets the nearest points be used at all
  have hf₁ : Metric.hausdorffEDist (toEuclidean '' S₁) (toEuclidean '' T₁) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hne _ hS₁ne) (hne _ hT₁ne)
      (himg _ hS₁).isBounded (himg _ hT₁).isBounded
  have hf₂ : Metric.hausdorffEDist (toEuclidean '' S₂) (toEuclidean '' T₂) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hne _ hS₂ne) (hne _ hT₂ne)
      (himg _ hS₂).isBounded (himg _ hT₂).isBounded
  rw [hausdorffDist₂, hausdorffDist₂, hausdorffDist₂, aux_toEuclidean_image_add,
    aux_toEuclidean_image_add]
  refine Metric.hausdorffDist_le_of_mem_dist
    (add_nonneg Metric.hausdorffDist_nonneg Metric.hausdorffDist_nonneg)
    (fun _ hx => aux_exists_mem_add_add_dist_le (himg _ hT₁) (hne _ hT₁ne) (himg _ hT₂)
      (hne _ hT₂ne) hf₁ hf₂ hx) (fun x hx => ?_)
  -- the other side is the same statement with the two families exchanged
  obtain ⟨y, hy, hxy⟩ := aux_exists_mem_add_add_dist_le (himg _ hS₁) (hne _ hS₁ne) (himg _ hS₂)
    (hne _ hS₂ne) (by rwa [Metric.hausdorffEDist_comm]) (by rwa [Metric.hausdorffEDist_comm]) hx
  refine ⟨y, hy, ?_⟩
  rw [Metric.hausdorffDist_comm (s := toEuclidean '' S₁),
    Metric.hausdorffDist_comm (s := toEuclidean '' S₂)]
  exact hxy

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
