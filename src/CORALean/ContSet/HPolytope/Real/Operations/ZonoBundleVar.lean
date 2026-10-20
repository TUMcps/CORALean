module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# `HPolytope.ZonoBundleVar`: the variable of CORA's polytope/zonotope-bundle program

The variable `(x, y, a₁, …, a_q)` of `aux_isIntersecting_P_zB` in CORA's
`@polytope/isIntersecting_.m`: a point `x`, one slack `yᵣ` per inequality row of the polytope
(`m` of them) and the coefficients `aᵢ` of each zonotope of the bundle.

## Inputs
* `m` – natural number
* `zB` – zonotope bundle

## Output
* the variable `(x, y, a₁, …, a_q)`, `y` with `m` slacks
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The variable `(x, y, a₁, …, a_q)`, `y` with `m` slacks. -/
abbrev HPolytope.ZonoBundleVar (m : ℕ) (zB : ZonoBundle (Vec ℝ n)) : Type :=
  Vec ℝ n × (Fin m → ℝ) × ((i : Fin zB.k) → Fin (zB.Z i).h → ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
