import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.translate`

Shifting by a point: every bound moves by what its own constraint reads off the
shift, and the constraint matrix is untouched.

Exact, and the case `comap` cannot reach — `comap` precomposes with a *linear*
map, and a translation is affine. Composed with `and` this is CORA's `plus`
against a single point, which is the one Minkowski sum a halfspace description
can take without enumerating vertices.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.translate (t : α) (P : HPolytope α) : HPolytope α where
  m := P.m
  A := P.A
  b := fun i => P.b i + P.A i t
  me := P.me
  Ae := P.Ae
  be := fun i => P.be i + P.Ae i t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
