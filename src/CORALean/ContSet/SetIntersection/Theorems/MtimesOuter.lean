module

public import CORALean.ContSet.SetIntersection.Operations.Mtimes
public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# `SetIntersection.mtimes` over-approximates the linear image

`M (⋂ᵢ Sᵢ) ⊆ ⋂ᵢ M Sᵢ`: a point of the intersection lies in every branch, so
its image under any `A` from `construct M` lies in every branch's own image,
`Mtimes.mtimes_outer` reading that into the mapped branch. At `sets = []` both
sides are `univ`, and the image of `univ` sits in `univ` for free.

## Inputs
* `m` – rows of the matrix
* `n` – columns of the matrix
* `M` – matrix
* `I` – intersection

## Hypotheses
* none

## Conclusion
* the linear image of `I` lies in the result
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {𝕄 : ℕ → ℕ → Type} {S : ℕ → Type}
  [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SetIntersection.mtimes_outer {m n : ℕ} (M : 𝕄 m n) (I : SetIntersection (S n)) :
    (⋃ A ∈ ContSet.construct M, (A *ᵥ ·) '' ContSet.construct I) ⊆
      ContSet.construct (SetIntersection.mtimes M I) := by -- --- PROOF ---
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx
  obtain ⟨A, hA, a, ha, rfl⟩ := hx
  have ha := SetIntersection.mem_construct.mp ha
  refine SetIntersection.mem_construct.mpr ?_
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  refine Mtimes.mtimes_outer M s ?_
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨A, hA, a, ha s hs, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
