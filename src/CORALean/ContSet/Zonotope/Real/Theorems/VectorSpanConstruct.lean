module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section

/-!
# The affine hull of a zonotope is spanned by its generators

The direction of the affine hull of `Z = c + ∑ βⱼgⱼ, |βⱼ| ≤ 1` is the span of its generators: a
difference of two points is a combination of generators, and each `gⱼ` is the difference of
`c + gⱼ` and `c`. So the dimension of a zonotope, which [1, Def. 1.3] takes to be that of the
span of its generators, is that of its affine hull, which is how `Zonotope.degree` measures a
face; with `construct_face`, a face's dimension is the rank of the generators `u` annihilates.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the direction of the affine hull is the generator span

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 1.3]: the direction of the affine hull of `Z` is the span of its generators. -/
theorem Zonotope.vectorSpan_construct (Z : Zonotope α) :
    vectorSpan ℝ Z.construct = Submodule.span ℝ (Set.range Z.G) := by -- --- PROOF ---
  classical
  apply le_antisymm
  · -- a difference of two points is a combination of generators
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨_, ⟨β, -, rfl⟩, _, ⟨γ, -, rfl⟩, rfl⟩
    have h : (Z.c + ∑ j, β j • Z.G j) -ᵥ (Z.c + ∑ j, γ j • Z.G j)
        = ∑ j, (β j - γ j) • Z.G j := by
      rw [vsub_eq_sub, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (sub_smul _ _ _).symm
    show _ -ᵥ _ ∈ _
    rw [h]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · -- each generator is the difference of `c + gⱼ` and `c`
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : Z.c + Z.G j ∈ Z.construct := by
      refine ⟨Pi.single j 1, fun i => ?_, ?_⟩
      · by_cases hi : i = j
        · subst hi
          simp
        · simp [hi]
      · simp [Pi.single_apply]
    have h0 : Z.c ∈ Z.construct := ⟨0, fun _ => by simp, by simp⟩
    have := vsub_mem_vectorSpan ℝ h1 h0
    rwa [vsub_eq_sub, add_sub_cancel_left] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
