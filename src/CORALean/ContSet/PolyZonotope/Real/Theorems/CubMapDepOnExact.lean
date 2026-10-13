import CORALean.ContSet.PolyZonotope.Real.Theorems.CubMapDepPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# `cubMapDepOn` is exactly the cubic map over the factors

What exactness means here: `construct (cubMapDepOn π₁ π₂ π₃ T P)` is the image of the admissible
factors `a` under `a ↦ cubEvalMixed T (π₁ (P.point a)) (π₂ (P.point a)) (π₃ (P.point a))`, all
three arguments at the same factors. The result has an empty independent block, so its set is
the image of the factors alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cubMapDepOn_exact (π₁ π₂ π₃ : V →ₗ[ℝ] Vec ℝ n)
    (T : Fin m → Fin n → Mat ℝ n n) (P : PolyZonotope V) :
    (fun a : Fin P.p → ℝ =>
        cubEvalMixed T (π₁ (P.point a)) (π₂ (P.point a)) (π₃ (P.point a)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (cubMapDepOn π₁ π₂ π₃ T P).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  -- a point at admissible factors is a member of the result
  · rintro _ ⟨a, ha, rfl⟩
    show cubEvalMixed T (π₁ (P.point a)) (π₂ (P.point a)) (π₃ (P.point a)) ∈ _
    rw [← PolyZonotope.cubMapDepOn_point]
    exact PolyZonotope.point_mem_construct _ ha
  -- and every member is such a point, the independent block being empty
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := PolyZonotope.exists_point_of_q_zero (cubMapDepOn π₁ π₂ π₃ T P) rfl hx
    exact ⟨a, ha, (PolyZonotope.cubMapDepOn_point π₁ π₂ π₃ T P a).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
