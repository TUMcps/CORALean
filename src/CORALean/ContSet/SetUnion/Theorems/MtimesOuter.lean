module

public import CORALean.ContSet.SetUnion.Operations.Mtimes
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `SetUnion.mtimes` over-approximates the linear image

Sound unconditionally, and without help from the member's own guarantee being
tight: a point of the image comes from some branch, `Mtimes.mtimes_outer`
reads it back into that branch's own image, mapped, and the union of images is
still contained in the union of the mapped branches.

## Inputs
* `m` – rows of the matrix
* `n` – columns of the matrix
* `M` – matrix
* `u` – union

## Hypotheses
* none

## Conclusion
* the linear image of `u` lies in the result
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

theorem SetUnion.mtimes_outer {m n : ℕ} (M : 𝕄 m n) (u : SetUnion (S n)) :
    (⋃ A ∈ ContSet.construct M, (A *ᵥ ·) '' ContSet.construct u) ⊆
      ContSet.construct (SetUnion.mtimes M u) := by -- --- PROOF ---
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx
  obtain ⟨A, hA, a, ha, rfl⟩ := hx
  obtain ⟨s, hs, ha⟩ := SetUnion.mem_construct.mp ha
  refine SetUnion.mem_construct.mpr ⟨Mtimes.mtimes M s, List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
  refine Mtimes.mtimes_outer M s ?_
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨A, hA, a, ha, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
