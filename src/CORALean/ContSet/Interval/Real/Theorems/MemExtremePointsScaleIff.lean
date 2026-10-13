import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff
import Mathlib.Tactic.Linarith

/-!
# Scaling a hyperplane to `Σᵢ xᵢ = α`

[1, Sec. 6.3 (scaling)]: the box `[0, b₁] × … × [0, bₙ]` cut by `Σᵢ βᵢxᵢ = α`, every `βᵢ ≠ 0`,
maps to `B⋆ = [0, β₁b₁] × … × [0, βₙbₙ]` cut by `Σᵢ xᵢ = α`, a solution `c⋆` of the latter to
`c = (c⋆₁/β₁, …, c⋆ₙ/βₙ)`. For a negative `βᵢ` the printed `[0, βᵢbᵢ]` has its bounds crossed;
read as the interval between them, `[min(0, βᵢbᵢ), max(0, βᵢbᵢ)]`, as CORA's `aux_boxScaling`
does, the vertices of the two cuts correspond exactly, by `c⋆ = (β₁c₁, …, βₙcₙ)`.
`Interval.scale_box_counterexample` is the crossed reading.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One coordinate: `x ∈ [0, b]` iff `βx` lies between `0` and `βb`, and at a bound iff `βx` is. -/
theorem aux_scale_coord {β bb x : ℝ} (hβ : β ≠ 0) (hbb : 0 ≤ bb) :
    ((0 ≤ x ∧ x ≤ bb) ↔ (min 0 (β * bb) ≤ β * x ∧ β * x ≤ max 0 (β * bb))) ∧
    ((x = 0 ∨ x = bb) ↔
      (β * x = min 0 (β * bb) ∨ β * x = max 0 (β * bb))) := by -- --- PROOF ---
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  -- `β < 0`: `[0, bb]` maps onto `[βbb, 0]`, the bounds swapping
  · have hmin : min 0 (β * bb) = β * bb := min_eq_right (by nlinarith)
    have hmax : max 0 (β * bb) = 0 := max_eq_left (by nlinarith)
    rw [hmin, hmax]
    refine ⟨⟨fun ⟨h1, h2⟩ => ⟨by nlinarith, by nlinarith⟩, fun ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩, ?_⟩
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
    · constructor
      · rintro (h | h)
        · right; rw [h, mul_zero]
        · left; rw [h]
      · rintro (h | h)
        · right; exact mul_left_cancel₀ hβ h
        · left; exact (mul_eq_zero.mp h).resolve_left hβ
  -- `β > 0`: the bounds keep their order
  · have hmin : min 0 (β * bb) = 0 := min_eq_left (by nlinarith)
    have hmax : max 0 (β * bb) = β * bb := max_eq_right (by nlinarith)
    rw [hmin, hmax]
    refine ⟨⟨fun ⟨h1, h2⟩ => ⟨by nlinarith, by nlinarith⟩, fun ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩, ?_⟩
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
    · constructor
      · rintro (h | h)
        · left; rw [h, mul_zero]
        · right; rw [h]
      · rintro (h | h)
        · left; exact (mul_eq_zero.mp h).resolve_left hβ
        · right; exact mul_left_cancel₀ hβ h


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mem_extremePoints_scale_iff {b β : Vec ℝ n} (hb0 : ∀ i, 0 ≤ b i)
    (hβ : ∀ i, β i ≠ 0) {α : ℝ} {c : Vec ℝ n} :
    c ∈ Set.extremePoints ℝ ((⟨0, b⟩ : Interval (Vec ℝ n)).construct ∩
        Interval.hyperplane β α) ↔
      (fun i => β i * c i) ∈ Set.extremePoints ℝ
        ((⟨fun i => min 0 (β i * b i), fun i => max 0 (β i * b i)⟩ :
          Interval (Vec ℝ n)).construct ∩ Interval.hyperplane 1 α) := by -- --- PROOF ---
  rw [Interval.mem_extremePoints_inter_hyperplane_iff hβ,
    Interval.mem_extremePoints_inter_hyperplane_iff (a := 1) (fun _ => by simp)]
  have hco := fun i => aux_scale_coord (x := c i) (hβ i) (hb0 i)
  have hbox : c ∈ (⟨0, b⟩ : Interval (Vec ℝ n)).construct ↔
      (fun i => β i * c i) ∈ (⟨fun i => min 0 (β i * b i), fun i => max 0 (β i * b i)⟩ :
        Interval (Vec ℝ n)).construct :=
    ⟨fun h i => (hco i).1.mp (h i), fun h i => (hco i).1.mpr (h i)⟩
  have hplane : c ∈ Interval.hyperplane β α ↔ (fun i => β i * c i) ∈ Interval.hyperplane 1 α := by
    simp [Interval.hyperplane]
  have hedge : (⟨0, b⟩ : Interval (Vec ℝ n)).OnEdge c ↔
      (⟨fun i => min 0 (β i * b i), fun i => max 0 (β i * b i)⟩ :
        Interval (Vec ℝ n)).OnEdge (fun i => β i * c i) := by
    have hk : ∀ k, (c k = (0 : Vec ℝ n) k ∨ c k = b k) ↔
        (β k * c k = min 0 (β k * b k) ∨ β k * c k = max 0 (β k * b k)) := fun k => by
      simpa only [Pi.zero_apply] using (hco k).2
    simp only [Interval.OnEdge, hk]
  rw [Set.mem_inter_iff, Set.mem_inter_iff, hbox, hplane, hedge]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
