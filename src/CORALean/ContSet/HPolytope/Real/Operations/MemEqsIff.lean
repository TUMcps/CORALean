import CORALean.ContSet.HPolytope.Real.Operations.Eqs

/-!
# Membership in `HPolytope.eqs`
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {q n : ℕ}

theorem HPolytope.mem_eqs_iff {Ae : Mat ℝ q n} {be : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.eqs Ae be).construct ↔ ∀ i, (Ae *ᵥ x) i = be i :=
  ⟨fun h i => h.2 i, fun h => ⟨fun i => i.elim0, h⟩⟩

end CORALean.Real
