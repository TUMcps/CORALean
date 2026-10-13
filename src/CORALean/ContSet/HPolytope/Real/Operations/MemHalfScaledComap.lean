import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.MemHalfScaledIff

/-!
# A weighted point meets the weighted constraints

The step every convex combination of two polytope-constrained sets takes: a
point whose block is `w • y` for a member `y`, with the parameter naming that
same `w`, satisfies the scaled rows — each of them is an unscaled row times a
nonnegative weight.

Stated at `comap` rather than at `halfScaled` alone: the block is what a caller
has a member of, and it reaches the constraints only through the map that reads
it off.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_halfScaled_comap {f : γ →ₗ[ℝ] α} {t : γ →ₗ[ℝ] ℝ} {P : HPolytope α}
    {x : γ} {w : ℝ} {y : α} (hw : (t x + 1) / 2 = w) (hw0 : 0 ≤ w) (hy : y ∈ P.construct)
    (hf : f x = w • y) : x ∈ ((P.comap f).halfScaled t).construct := by -- --- PROOF ---
  refine HPolytope.mem_halfScaled_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
  -- the rows of the preimage are `P`'s own, read at the block
  · show P.A i (f x) ≤ (t x + 1) / 2 * P.b i
    rw [hf, hw, map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hy.1 i) hw0
  · show P.Ae i (f x) = (t x + 1) / 2 * P.be i
    rw [hf, hw, map_smul, smul_eq_mul, hy.2 i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
