module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# A hull as a constrained zonotope

## Inputs
* `k` – number of vertices

## Output
* standard simplex as halfspace constraints
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The standard simplex as constraints: nonnegative, summing to one. -/
def VPolytope.simplex (k : ℕ) : HPolytope (Vec ℝ k) where
  m := k
  A := fun j => -LinearMap.proj j
  b := fun _ => 0
  me := 1
  Ae := fun _ => ∑ j, LinearMap.proj j
  be := fun _ => 1

/-- The constrained zonotope of a hull: the vertices as generators around the origin, with the
coefficients constrained to the simplex. -/
def VPolytope.conZonotope (P : VPolytope α) : ConZonotope α where
  h := P.k
  c := 0
  G := P.V
  P := VPolytope.simplex P.k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
