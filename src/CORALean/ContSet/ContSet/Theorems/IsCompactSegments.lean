import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The segments between two compact sets are compact

`segments X Y` is the image of `X × Y × [0,1]` under `(y₁,y₂,λ) ↦ λy₁ + (1-λ)y₂`,
so compactness of the two operands carries over. Stated in a normed space, the
only structure the continuity of that map needs beyond the module `segments`
itself is written against.

This is what lets a Hausdorff bound stated against `segments` be read back as a
witness: a compact set attains its infimum distance, and `≤` on a Hausdorff
distance gives an actual nearby point only where it does.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set of all segments running from one compact set to another is compact. -/
theorem isCompact_segments {X Y : Set α} (hX : IsCompact X) (hY : IsCompact Y) :
    IsCompact (segments X Y) := by -- --- PROOF ---
  have himg : segments X Y
      = (fun p : (α × α) × ℝ => p.2 • p.1.1 + (1 - p.2) • p.1.2)
        '' ((X ×ˢ Y) ×ˢ Set.Icc (0:ℝ) 1) := by
    ext x
    constructor
    · rintro ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
      exact ⟨((y₁, y₂), lam), ⟨⟨hy₁, hy₂⟩, hlam⟩, rfl⟩
    · rintro ⟨⟨⟨y₁, y₂⟩, lam⟩, ⟨⟨hy₁, hy₂⟩, hlam⟩, rfl⟩
      exact ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  rw [himg]
  exact ((hX.prod hY).prod isCompact_Icc).image (by fun_prop)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
