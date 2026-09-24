import CORALean.ContSet.SetUnion.Theorems.MtimesOuter

/-!
# `SetUnion.mtimes` is exact when every branch's own `mtimes` is

Not a class obligation — `Mtimes` only ever asks for the outer bound — but the
member's exactness reads straight across: the reverse inclusion pulls a point
of the mapped union back to its branch, replaces the branch's own image by the
branch itself via `hExact`, and re-covers it as a point of the original union.
`mtimes_outer` supplies the direction this adds nothing to.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {𝕄 : ℕ → ℕ → Type} {S : ℕ → Type}
  [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SetUnion.mtimes_exact
    (hExact : ∀ {m n : ℕ} (M : 𝕄 m n) (s : S n),
      (⋃ A ∈ ContSet.construct M, (A *ᵥ ·) '' ContSet.construct s) =
        ContSet.construct (Mtimes.mtimes M s))
    {m n : ℕ} (M : 𝕄 m n) (u : SetUnion (S n)) :
    (⋃ A ∈ ContSet.construct M, (A *ᵥ ·) '' ContSet.construct u) =
      ContSet.construct (SetUnion.mtimes M u) := by -- --- PROOF ---
  refine Set.Subset.antisymm (SetUnion.mtimes_outer M u) ?_
  intro x hx
  obtain ⟨t, ht, hx⟩ := SetUnion.mem_construct.mp hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hx' : x ∈ ⋃ A ∈ ContSet.construct M, (A *ᵥ ·) '' ContSet.construct s := by
    rw [hExact M s]; exact hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx'
  obtain ⟨A, hA, a, ha, rfl⟩ := hx'
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨A, hA, a, SetUnion.mem_construct.mpr ⟨s, hs, ha⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
