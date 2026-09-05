import CORALean.ContSet.HPolytope.Real.Operations.Ineqs

/-!
# Membership in `HPolytope.ineqs`
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {q n : ℕ}

theorem HPolytope.mem_ineqs_iff {A : Mat ℝ q n} {b : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.ineqs A b).construct ↔ ∀ i, (A *ᵥ x) i ≤ b i :=
  ⟨fun h i => h.1 i, fun h => ⟨h, fun i => i.elim0⟩⟩

end CORALean.Real
