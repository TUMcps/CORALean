import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.comap`

The preimage under a linear map: every constraint is precomposed, the counts
untouched. Exact, and the reason CORA's `mtimes` on a halfspace description asks
for an invertible matrix — it is this at `M⁻¹`.

The direction a halfspace description goes. A vertex description goes the other
way, which is `VPolytope.map`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

def HPolytope.comap (f : β →ₗ[ℝ] α) (P : HPolytope α) : HPolytope β where
  m := P.m
  A := fun i => (P.A i).comp f
  b := P.b
  me := P.me
  Ae := fun i => (P.Ae i).comp f
  be := P.be

end CORALean.Real
