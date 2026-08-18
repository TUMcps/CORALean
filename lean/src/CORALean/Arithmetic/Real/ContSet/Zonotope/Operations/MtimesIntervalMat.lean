import CORALean.Arithmetic.Real.ContSet.Zonotope.Operations.Mtimes
import CORALean.Arithmetic.Real.MatSet.API

/-!
# Zonotopes: multiplication by an interval matrix

CORA writes this as `mtimes` too, dispatching on the argument. The centre acts
exactly, as a matrix does, and everything the radius allows is boxed into `n`
fresh generators — one per coordinate, so the cost is `n` generators a step and
not more.

`absBound` is what makes that box computable: a coordinate of a zonotope never
leaves `|c| + Σ|g|`, which is the interval hull read off without building it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix

variable {m n : ℕ}

/-- How far coordinate `j` can reach from the origin. -/
def Zonotope.absBound (Z : Zonotope n) (j : Fin n) : ℝ :=
  |Z.c j| + ∑ l, |Z.G j l|

/-- What the radius can add to coordinate `i`, over every matrix denoted. -/
noncomputable def Zonotope.radiusReach (IM : IntervalMat m n) (Z : Zonotope n) (i : Fin m) : ℝ :=
  ∑ j, IM.radius i j * Z.absBound j

noncomputable def Zonotope.mtimesIntervalMat (IM : IntervalMat m n) (Z : Zonotope n) :
    Zonotope m where
  h := Z.h + m
  c := IM.center *ᵥ Z.c
  G := fun i => Fin.append ((IM.center * Z.G) i)
                  (Matrix.diagonal (fun i => Zonotope.radiusReach IM Z i) i)

end CORALean.Arithmetic.Real
