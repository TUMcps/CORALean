module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.ofEqs1D`: a one-dimensional polytope from equality rows

The polytope `{x ∈ ℝ¹ | Ae i * x = be i for all i}`, no inequality rows: the column vectors
`Ae`, `be` of a 1-D CORA polytope's equality constraints.

## Inputs
* `k` – natural number
* `Ae` – real numbers indexed by `Fin k`
* `be` – real numbers indexed by `Fin k`

## Output
* the one-dimensional polytope of the equality rows `Ae i * x = be i` and no inequality
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The one-dimensional polytope of the equality rows `Ae i * x = be i` and no inequality. -/
def HPolytope.ofEqs1D {k : ℕ} (Ae be : Fin k → ℝ) : HPolytope (Vec ℝ 1) where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := k
  Ae := fun i => Ae i • (LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ)
  be := be

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
