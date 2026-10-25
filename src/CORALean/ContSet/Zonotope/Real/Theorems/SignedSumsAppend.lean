module

public import CORALean.ContSet.Zonotope.Real.Operations.SignedSums
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `Z±` of concatenated generators is the sum of the `Z±`

[1, Remark 3]: `Z±([R₁, R₂]) = Z±(R₁) ⊕ Z±(R₂)`. With a box `[r]` as the centered zonotope with
generators `diag(rad)`, the potential vertices of an MSPB `A [r] + [v]` are the images of the
boxes' vertices (`A [r]± ⊕ [v]±`), which is how `Zonotope.mspb` enumerates them.

## Inputs
* `R₁` – first family of vectors
* `R₂` – second family of vectors

## Hypotheses
* none

## Conclusion
* signed sums of the concatenation are the sum of the two sets

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on Automatic
      Control, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

open scoped Pointwise

namespace CORALean.Real

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.signedSums_append (R₁ : Fin p → Vec ℝ n) (R₂ : Fin q → Vec ℝ n) : -- --- CONCL ---
    Zonotope.signedSums (Fin.append R₁ R₂) =
      Zonotope.signedSums R₁ + Zonotope.signedSums R₂ := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨_, ⟨fun i => σ (Fin.castAdd q i), rfl⟩, _, ⟨fun i => σ (Fin.natAdd p i), rfl⟩, ?_⟩
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  · rintro ⟨_, ⟨σ₁, rfl⟩, _, ⟨σ₂, rfl⟩, rfl⟩
    refine ⟨Fin.append σ₁ σ₂, ?_⟩
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
