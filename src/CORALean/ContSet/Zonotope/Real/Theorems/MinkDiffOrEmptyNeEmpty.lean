module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffOrEmpty

@[expose] public section

/-!
# `Zonotope.minkDiffOrEmpty` is empty only where nothing certifies

What stops the operation from being the useless one that always answers `∅`,
which `MinkDiff`'s inner obligation would accept as readily: one certified
generator representation anywhere is enough to make the result a zonotope.

Which zonotope it is stays open — the choice is the definition's, not the
caller's — so this says the result is not empty and nothing about its size.
`Examples/MinkowskiDifference` supplies a pair and an `M` that certifies.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffOrEmpty_ne_empty (Z₁ Z₂ : Zonotope α)
    (h : ∃ M, (Z₁.minkDiffRep Z₂ M).isSome) : Z₁.minkDiffOrEmpty Z₂ ≠ OptEmpty.empty := by
  rw [Zonotope.minkDiffOrEmpty, dif_pos h]
  intro hc
  cases hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
