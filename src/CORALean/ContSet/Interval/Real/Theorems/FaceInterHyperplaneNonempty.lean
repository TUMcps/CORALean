module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# An s-face below and above the plane holds a solution

[1, Cor. 6.3 (3)]: for `j < n`, solutions of the face `F = {v₁} × … × {v_j} × [0, b_{j+1}] × … ×
[0, bₙ]` exist if `Σ_{i≤j} vᵢ < α` and `Σ_{i≤j} vᵢ + Σ_{i>j} bᵢ ≥ α`. The face is a box, its
lowest corner below the plane and its highest one not, and the segment between them crosses
it. Eq. (5) is not needed.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.face_inter_hyperplane_nonempty {b : Vec ℝ n} (hb0 : ∀ i, 0 ≤ b i) {j : ℕ}
    (p : Fin n → Bool) {α : ℝ} :
    let w := (⟨0, b⟩ : Interval (Vec ℝ n)).corner fun i => if (i : ℕ) < j then p i else false
    let F : Interval (Vec ℝ n) := ⟨w, fun i => if (i : ℕ) < j then w i else b i⟩
    ∑ i, w i < α → α ≤ ∑ i, F.sup i →
      (F.construct ∩ Interval.hyperplane 1 α).Nonempty := by -- --- PROOF ---
  intro w F hlo hhi
  have hwF : ∀ i, w i ≤ F.sup i := fun i => by
    simp only [F]
    split_ifs with hi
    · exact le_rfl
    · simp [w, Interval.corner, hi, hb0 i]
  have hgap : 0 < ∑ i, F.sup i - ∑ i, w i := by linarith
  -- the point a fraction `θ` of the way from the lowest corner to the highest
  set θ := (α - ∑ i, w i) / (∑ i, F.sup i - ∑ i, w i) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hgap.le
  have hθ1 : θ ≤ 1 := (div_le_one hgap).mpr (by linarith)
  refine ⟨fun i => w i + θ * (F.sup i - w i), fun i => ?_, ?_⟩
  · have hd := hwF i
    change w i ≤ w i + θ * (F.sup i - w i) ∧ w i + θ * (F.sup i - w i) ≤ F.sup i
    constructor <;> nlinarith
  · show ∑ i, (1 : Vec ℝ n) i * (w i + θ * (F.sup i - w i)) = α
    simp only [Pi.one_apply, one_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib]
    rw [hθ, div_mul_cancel₀ _ hgap.ne']
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
