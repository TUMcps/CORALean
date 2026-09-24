import CORALean.ContSet.SetUnion.SetUnion

/-!
# `SetUnion.plus`

Every pair of branches, one from each operand, summed: CORA has no bundle to
model this against, but the shape is `ZonoBundle.plus`'s, read at `⋃` instead
of `⋂` — `(⋃ Aᵢ) + (⋃ Bⱼ)` is exactly `⋃ᵢⱼ (Aᵢ + Bⱼ)`, so pairing every branch
loses nothing a union-shaped result could keep.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Plus S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every pair of branches, summed. -/
def SetUnion.plus (u v : SetUnion S) : SetUnion S :=
  ⟨(u.sets ×ˢ v.sets).map fun p => Plus.plus p.1 p.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
