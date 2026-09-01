import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContDynamics.LinearSys.MatExp.API

/-!
# Zonotopes: multiplication by an interval matrix

CORA writes this as `mtimes` too, dispatching on the argument. The centre acts
exactly, as a matrix does, and everything the radius allows is boxed into one
fresh generator per coordinate — so a step costs `n` generators and no more.

`absBound` is what makes that box computable: a coordinate of a zonotope never
leaves `|c| + Σ|g|`, the interval hull read off without building it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {m n : ℕ}

/-- How far coordinate `j` can reach from the origin. -/
def Zonotope.absBound (Z : Zonotope (Vec ℝ n)) (j : Fin n) : ℝ :=
  |Z.c j| + ∑ l, |Z.G l j|

/-- What the radius can add to coordinate `i`, over every matrix denoted. -/
noncomputable def Zonotope.radiusReach (IM : Interval (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n))
    (i : Fin m) : ℝ :=
  ∑ j, IM.radius i j * Z.absBound j

noncomputable def Zonotope.mtimesIntervalMat (IM : Interval (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) where
  h := Z.h + m
  c := IM.center *ᵥ Z.c
  G := Fin.append (fun l => IM.center *ᵥ Z.G l)
        (Matrix.diagonal fun i => Zonotope.radiusReach IM Z i)

end CORALean.Real
