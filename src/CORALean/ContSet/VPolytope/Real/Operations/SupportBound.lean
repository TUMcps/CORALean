import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.Global.LinProg.API

/-!
# A vertex description answers a linear program without solving one

Where a halfspace description needs a dual solution to bound a direction, a
vertex description reads the answer off its own data: the weights are
nonnegative and sum to one, so a combination cannot reach past the furthest
vertex. That is the whole content of the LP here, and the maximum is attained
rather than merely approached.

This is the reason the two representations are kept apart, and the reason the
conversion between them is cheap in exactly one direction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem VPolytope.le_of_forall_le (P : VPolytope α) (c : α →ₗ[ℝ] ℝ) {v : ℝ}
    (h : ∀ l, c (P.V l) ≤ v) {x : α} (hx : x ∈ P.construct) : c x ≤ v := by
  obtain ⟨β, hβ, hsum, rfl⟩ := hx
  rw [map_sum]
  calc ∑ l, c (β l • P.V l) = ∑ l, β l * c (P.V l) :=
        Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
    _ ≤ ∑ l, β l * v := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hβ l)
    _ = v := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Noncomputable only in the supremum: over a finite vertex list the value is a
maximum, and the float layer computes it as one. -/
noncomputable def VPolytope.supportBound (P : VPolytope α) (c : α →ₗ[ℝ] ℝ) :
    SupportBound P.construct c where
  val := ⨆ l, c (P.V l)
  -- the function spelt out: `le_ciSup` cannot guess it from the goal
  le _ hx := P.le_of_forall_le c
    (fun l => le_ciSup (f := fun l => c (P.V l)) (Set.finite_range _).bddAbove l) hx

end CORALean.Real
