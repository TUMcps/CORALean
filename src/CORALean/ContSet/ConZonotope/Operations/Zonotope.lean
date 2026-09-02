import CORALean.ContSet.ConZonotope.ConZonotope

/-!
# Between a zonotope and a constrained one

CORA's `zonotope(cZ)` forgets the constraints, which is an enclosure, and its
constructor from a zonotope adds none, which is exact. Both directions live here
rather than in `Zonotope`, so that deleting this representation leaves that one
untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.zonotope (C : ConZonotope α) : Zonotope α where
  h := C.h
  c := C.c
  G := C.G

def Zonotope.conZonotope (Z : Zonotope α) : ConZonotope α where
  h := Z.h
  c := Z.c
  G := Z.G
  P := HPolytope.fullspace _

end CORALean.Real
