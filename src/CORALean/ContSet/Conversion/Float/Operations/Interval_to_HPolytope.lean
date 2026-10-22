module

public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# A box as halfspaces, over a floating-point scalar

## Inputs
* `𝕋` – scalar type
* `n` – dimension

## Output
* identity matrix, as a constraint matrix
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The identity, and the identity negated: the only two constraint matrices a
box needs. -/
def identityMat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : Mat 𝕋 n n :=
  fun i j => if i = j then one else zero

/-- The negated identity matrix, the constraint matrix of the lower bounds. -/
def negIdentityMat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : Mat 𝕋 n n :=
  fun i j => if i = j then neg one else zero

/-- The halfspace description of a box: an upper bound `x ≤ sup` and a lower bound `-x ≤ -inf` per
coordinate. -/
def Interval.hPolytope (I : Interval (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  (HPolytope.ineqs (identityMat 𝕋 n) I.sup).stackRows
    (HPolytope.ineqs (negIdentityMat 𝕋 n) (-I.inf))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
