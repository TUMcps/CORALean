module

public import CORALean.ContSet.SetUnion.Theorems.MtimesOuter

@[expose] public section

/-!
# `SetUnion.mtimes` is exact when every branch's own `mtimes` is

Not a class obligation — `Mtimes` only ever asks for the outer bound — but the
member's exactness reads straight across: the reverse inclusion pulls a point
of the mapped union back to its branch, replaces the branch's own image by the
branch itself via `hExact`, and re-covers it as a point of the original union.
`mtimes_outer` supplies the direction this adds nothing to.

## Inputs
* `m` – rows of the matrix
* `n` – columns of the matrix
* `M` – matrix
* `u` – union

## Hypotheses
* `hExact` – `mtimes` is exact on each branch

## Conclusion
* the linear image of `u` is exactly the result
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {𝕄 : ℕ → ℕ → Type} {S : ℕ → Type}
  [∀ m n, ContSetLike (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSetLike (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SetUnion.mtimes_exact
    (hExact : ∀ {m n : ℕ} (M : 𝕄 m n) (s : S n),
      (⋃ A ∈ ContSetLike.toSet M, (A *ᵥ ·) '' ContSetLike.toSet s) =
        ContSetLike.toSet (Mtimes.mtimes M s))
    {m n : ℕ} (M : 𝕄 m n) (u : SetUnion (S n)) : -- --- CONCL ---
    (⋃ A ∈ ContSetLike.toSet M, (A *ᵥ ·) '' ContSetLike.toSet u) =
      ContSetLike.toSet (SetUnion.mtimes M u) := by -- --- PROOF ---
  refine Set.Subset.antisymm (SetUnion.mtimes_outer M u) ?_
  intro x hx
  obtain ⟨t, ht, hx⟩ := SetUnion.mem_toSet.mp hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hx' : x ∈ ⋃ A ∈ ContSetLike.toSet M, (A *ᵥ ·) '' ContSetLike.toSet s := by
    rw [hExact M s]; exact hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx'
  obtain ⟨A, hA, a, ha, rfl⟩ := hx'
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨A, hA, a, SetUnion.mem_toSet.mpr ⟨s, hs, ha⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
