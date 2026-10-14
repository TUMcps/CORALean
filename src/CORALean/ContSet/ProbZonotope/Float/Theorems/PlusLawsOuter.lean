module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ConvMultivariateGaussian

@[expose] public section

/-!
# `ProbZonotope.plus` adds the laws

Outer: the convolution of a law of each operand (independent sums) is a law of the result: `N(a,
Σ₁) ∗ N(b, Σ₂) = N(a + b, Σ₁ + Σ₂)`, the means in the float zonotope sum and the covariances in
the interval-matrix sum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory Matrix WithLp FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.plus_laws_outer (P₁ P₂ : ProbZonotope 𝕋 n) :
    Set.image2 (· ∗ ·) P₁.laws P₂.laws ⊆ (P₁.plus P₂).laws := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a, ha, S₁, hS₁, hp₁, rfl⟩, _, ⟨b, hb, S₂, hS₂, hp₂, rfl⟩, rfl⟩
  refine ⟨a + b, Zonotope.plus_outer P₁.Z P₂.Z (Set.add_mem_add ha hb), S₁ + S₂,
    Interval.matPlus_outer _ _ hS₁ hS₂, hp₁.add hp₂, ?_⟩
  beta_reduce
  rw [Real.conv_multivariateGaussian _ _ hp₁ hp₂, ← WithLp.toLp_add]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
