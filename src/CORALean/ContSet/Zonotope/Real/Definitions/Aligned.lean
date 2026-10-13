import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Aligned zonotopes

[1, Def. 3]. `AlignedWith` is the printed relation: every generator of the
second zonotope points along one of the first's. `MutuallyAligned` is it in
both directions.

`NoAlignedGens` is the standing assumption the definition opens with, on each
operand separately — a zonotope whose own generators are pairwise
non-parallel. It is not a hypothesis of `AlignedWith`: the paper's reason for
it is that two parallel generators can be merged into one first, so it
normalizes the operands rather than constraining the relation, and
`minkDiffAligned` never asks for it either.

The scaling is unconstrained here, exactly as printed — which is what the
finding on `Prop. 5` is about: the closed form `minkDiffAligned` computes needs
`0 ≤ γ ≤ 1`, and `minkDiffAligned_not_inner` is the counterexample outside it.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- [1, Def. 3]'s standing assumption on one operand: no generator is a scaling
of another, two that are being merged into one before the relation is read. -/
def Zonotope.NoAlignedGens (Z : Zonotope α) : Prop :=
  ¬ ∃ i j : Fin Z.h, i ≠ j ∧ ∃ γ : ℝ, γ • Z.G i = Z.G j


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 3]: `Z₁` is aligned with `Z₂` when every generator of `Z₂` is a
scaling of some generator of `Z₁`. -/
def Zonotope.AlignedWith (Z₁ Z₂ : Zonotope α) : Prop :=
  ∀ i : Fin Z₂.h, ∃ j : Fin Z₁.h, ∃ γ : ℝ, γ • Z₁.G j = Z₂.G i

/-- [1, Def. 3]: aligned each way round. -/
def Zonotope.MutuallyAligned (Z₁ Z₂ : Zonotope α) : Prop :=
  Z₁.AlignedWith Z₂ ∧ Z₂.AlignedWith Z₁

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
