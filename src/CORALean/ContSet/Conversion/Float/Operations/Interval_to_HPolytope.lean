module

public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# A box as halfspaces, over a floating-point scalar — the construction

`identityMat`, `negIdentityMat` and `Interval.hPolytope` are the constructions;
`Interval_to_HPolytope` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
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

def negIdentityMat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : Mat 𝕋 n n :=
  fun i j => if i = j then neg one else zero

def Interval.hPolytope (I : Interval (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  (HPolytope.ineqs (identityMat 𝕋 n) I.sup).intersection
    (HPolytope.ineqs (negIdentityMat 𝕋 n) fun j => neg (I.inf j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
