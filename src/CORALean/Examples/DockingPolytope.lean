module

public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# The Docking safe set and its inner polytope

The safe set of the ARCH-COMP 2026 spacecraft Docking instance is a cone around the target in
`(sx, sy, vx, vy)`: `‖v‖₂ ≤ 0.2 + 2n ‖s‖₂`, with `n` the mean motion. It is not a polytope, so a
verifier that checks halfspaces needs one inside it: `dockingPolytope`, the rows
`cos φₖ vx + sin φₖ vy - w (sx + sy) ≤ 0.2 c`, `φₖ = 2πk/N`. It is inside the safe set for `c` at
most `cos(π/N)` and `w` between `0` and `c · 2n/√2` (`DockingPolytopeSubsetSafe`).

## Inputs
* `N` – number of sides
* `c` – radius factor of the polygon
* `w` – weight of `sx + sy`

## Output
* the polytope, and the safe set it approximates
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inner polytope of the Docking safe set, with `N` sides: the rows
`(-w, -w, cos φₖ, sin φₖ)` and the right-hand side `0.2 c`. -/
noncomputable def dockingPolytope (N : ℕ) (c w : ℝ) : Real.HPolytope (Vec ℝ 4) :=
  Real.HPolytope.ineqs
    (fun (k : Fin N) => ![-w, -w, Real.cos (2 * Real.pi * k / N), Real.sin (2 * Real.pi * k / N)])
    (fun _ => 1 / 5 * c)

/-- The safe set of the Docking instance in `(sx, sy, vx, vy)`: `‖v‖₂ ≤ 0.2 + 2n ‖s‖₂`. -/
def dockingSafeSet (n : ℝ) : Set (Vec ℝ 4) :=
  {x | √(x 2 ^ 2 + x 3 ^ 2) ≤ 1 / 5 + 2 * n * √(x 0 ^ 2 + x 1 ^ 2)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
