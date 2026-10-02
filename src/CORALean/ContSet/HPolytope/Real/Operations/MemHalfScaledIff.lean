import CORALean.ContSet.HPolytope.Real.Operations.HalfScaled
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Membership in `HPolytope.halfScaled`

The halved right-hand side read back as a weight on the original one. Stated as
an `iff` on points, which is the form a constrained zonotope's convex hull needs
it in: it has the weight in hand and owes the rows.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_halfScaled_iff {t : α →ₗ[ℝ] ℝ} {P : HPolytope α} {x : α} :
    x ∈ (P.halfScaled t).construct ↔
      (∀ i, P.A i x ≤ (t x + 1) / 2 * P.b i) ∧ ∀ i,
        P.Ae i x = (t x + 1) / 2 * P.be i := by -- --- PROOF ---
  -- each row is `A x - (b/2) t x` against `b/2`, which is the weight times `b`
  have hb (r : ℝ) : (t x + 1) / 2 * r = r / 2 * t x + r / 2 := by ring
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h := hle i
      simp only [HPolytope.halfScaled, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] at h
      rw [hb]
      linarith
    · have h := heq i
      simp only [HPolytope.halfScaled, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] at h
      rw [hb]
      linarith
  -- back, the same rearrangement in the other direction
  · rintro ⟨hle, heq⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h := hle i
      rw [hb] at h
      show P.A i x - P.b i / 2 * t x ≤ P.b i / 2
      linarith
    · have h := heq i
      rw [hb] at h
      show P.Ae i x - P.be i / 2 * t x = P.be i / 2
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
