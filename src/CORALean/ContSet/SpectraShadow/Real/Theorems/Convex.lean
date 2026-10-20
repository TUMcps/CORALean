module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

/-!
# A spectrahedral shadow is convex

Two points have two variable vectors, and their convex combination satisfies the
inequality at the same combination of them: the inequality is affine in the
variables and the positive semidefinite matrices are a convex cone, closed under
a sum and a nonnegative multiple. The point is the same combination of the two
projections, the projection being affine too.

This is what makes the representation sit beside the polytopes and ellipsoids as a
convex set, and the reason nothing here needs a convexity hypothesis.

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* A spectrahedral shadow is convex
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.convex_construct (S : SpectraShadow α) :
    Convex ℝ S.construct := by -- --- PROOF ---
  rintro _ ⟨β₁, h₁, rfl⟩ _ ⟨β₂, h₂, rfl⟩ a b ha hb hab
  -- the variables are the same combination of the two points'
  refine ⟨a • β₁ + b • β₂, ?_, ?_⟩
  · have h := (h₁.smul ha).add (h₂.smul hb)
    have hA : a • S.A₀ + b • S.A₀ = S.A₀ := by rw [← add_smul, hab, one_smul]
    have hE : S.A₀ + ∑ i, (a • β₁ + b • β₂) i • S.A i
        = a • (S.A₀ + ∑ i, β₁ i • S.A i) + b • (S.A₀ + ∑ i, β₂ i • S.A i) := by
      calc S.A₀ + ∑ i, (a • β₁ + b • β₂) i • S.A i
          = (a • S.A₀ + b • S.A₀) + ∑ i, (a • β₁ + b • β₂) i • S.A i := by rw [hA]
        _ = _ := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
            Finset.sum_add_distrib, smul_add, Finset.smul_sum]
          abel
    rw [hE]
    exact h
  -- and so is the point, the projection being affine too
  · have hc : a • S.c + b • S.c = S.c := by rw [← add_smul, hab, one_smul]
    calc a • (S.c + ∑ j, β₁ j • S.G j) + b • (S.c + ∑ j, β₂ j • S.G j)
        = (a • S.c + b • S.c) + ∑ j, (a • β₁ + b • β₂) j • S.G j := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
            Finset.sum_add_distrib, smul_add, Finset.smul_sum]
          abel
      _ = S.c + ∑ j, (a • β₁ + b • β₂) j • S.G j := by rw [hc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
