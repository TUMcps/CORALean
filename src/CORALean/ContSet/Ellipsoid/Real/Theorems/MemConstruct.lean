import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.mem_construct`

An introduction rather than a characterisation: any affine image of a unit
ball point is a point the ellipsoid contains. `Theorems/QMemConstruct` is the
same statement at `u = 0`, the centre.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mem_construct {E : Ellipsoid n} {u : Vec ℝ E.k} (hu : ‖u‖₂ ≤ 1) :
    E.q + E.G *ᵥ u ∈ E.construct := ⟨u, hu, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
