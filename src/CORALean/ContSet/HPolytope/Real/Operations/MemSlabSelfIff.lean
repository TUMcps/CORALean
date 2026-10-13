import CORALean.ContSet.HPolytope.Real.Operations.MemSlabIff

/-!
# An equality is the degenerate slab
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An equality is the degenerate slab, which is how CORA's `Ae x = be` reads in
this form. -/
theorem HPolytope.mem_slab_self_iff {Ae : Mat ℝ q n} {be : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.slab Ae be be).construct ↔ ∀ i, (Ae *ᵥ x) i = be i := by
  rw [HPolytope.mem_slab_iff]
  exact forall_congr' fun i => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
