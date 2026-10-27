module

public import CORALean.ContSet.Zonotope.Float.Operations.ContainsPoint
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.underapproximate`, over a floating-point scalar

CORA's `@zonotope/underapproximate(Z, S)`: for the direction `S i` the vertex
`c ± Σⱼ sign(S iᵀ gⱼ) gⱼ`. Here the candidate is computed in floats (one named `let` per step of
the real definition `Real.Zonotope.underapproximate`), and rounding may move it off the vertex; so
it is returned only if `Zonotope.containsPoint`, with a right inverse `H` of the generators the
caller proposes, certifies it inside the zonotope, else `none`. Sufficient only: `some` proves the
point is a member, `none` refutes nothing.

## Inputs
* `Z` – zonotope
* `H` – candidate right inverse
* `s` – direction
* `b` – plus or minus vertex

## Output
* vertex in the direction, if certified inside
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The candidate vertex for direction `s`; rounding may move it, `underapproximate` checks it. -/
@[step_of Zonotope.underapproximate]
def Zonotope.step_underapproximateCandidate (Z : Zonotope (Vec 𝕋 n)) (s : Vec 𝕋 n)
    (b : Bool) : Vec 𝕋 n :=
  let d := fun j : Fin Z.h => sumUp fun i => mulUp (s i) (Z.G j i)  -- sᵀ gⱼ
  let sgn := fun j : Fin Z.h =>  -- sign(sᵀ gⱼ), `0` unless strictly signed, flipped for `false`
    if le (d j) zero then (if le zero (d j) then zero else if b then neg one else one)
    else (if b then one else neg one)
  fun i => addUp (Z.c i) (sumUp fun j => mulUp (sgn j) (Z.G j i))


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.underapproximate (Z : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z.h n) (s : Vec 𝕋 n) (b : Bool) :
    Option (Vec 𝕋 n) :=
  let p := Z.step_underapproximateCandidate s b
  if Z.containsPoint H p then some p else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
