module

public import CORALean.ContSet.Zonotope.Float.Operations.ContainsPoint
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.underapproximate`, over a floating-point scalar

CORA's `@zonotope/underapproximate(Z, S)`: for the direction `S i` the vertex
`c ± Σⱼ sign(S iᵀ gⱼ) gⱼ`, computed in floats, where rounding may move it off the vertex. It is
returned only if `Zonotope.containsPoint`, at a right inverse `H` the caller proposes, certifies it
inside, or if its sums are exact (the sum rounded down equals the one rounded up, so the candidate
is the real point of its coefficients in `[-1, 1]`), else `none`. `containsPoint` reaches only a
ball about the center, of radius `1 / (4 ‖H‖)`, whose points have coefficients at most `1/4`, and
answered `none` at every vertex tried; the exactness test returns one. Sufficient only: `some`
proves membership, `none` refutes nothing.

## Inputs
* `Z` – zonotope
* `H` – candidate right inverse
* `s` – direction
* `b` – plus or minus vertex

## Output
* vertex in the direction, if certified inside
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   03-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The coefficient `sign(sᵀ gⱼ)` of generator `j`, as a float. -/
@[step_of Zonotope.underapproximate]
def Zonotope.step_underapproximateSign (Z : Zonotope (Vec 𝕋 n)) (s : Vec 𝕋 n) (b : Bool)
    (j : Fin Z.h) : 𝕋 :=
  let d := sumUp fun i => mulUp (s i) (Z.G j i)  -- sᵀ gⱼ
  -- sign(sᵀ gⱼ), `0` unless strictly signed, flipped for `false`
  if le d zero then (if le zero d then zero else if b then neg one else one)
  else (if b then one else neg one)

/-- The candidate vertex for direction `s`; rounding may move it, `underapproximate` checks it. -/
@[step_of Zonotope.underapproximate]
def Zonotope.step_underapproximateCandidate (Z : Zonotope (Vec 𝕋 n)) (s : Vec 𝕋 n)
    (b : Bool) : Vec 𝕋 n :=
  fun i => addUp (Z.c i) (sumUp fun j => mulUp (Z.step_underapproximateSign s b j) (Z.G j i))

/-- The same sums rounded down. -/
@[step_of Zonotope.underapproximate]
def Zonotope.step_underapproximateLower (Z : Zonotope (Vec 𝕋 n)) (s : Vec 𝕋 n)
    (b : Bool) : Vec 𝕋 n :=
  fun i => addDown (Z.c i) (sumDown fun j => mulDown (Z.step_underapproximateSign s b j) (Z.G j i))

/-- The candidate is the real point of its coefficients: the sums rounded down and up agree, and
the error box holds `0`. -/
@[step_of Zonotope.underapproximate]
def Zonotope.step_underapproximateExact (Z : Zonotope (Vec 𝕋 n)) (s : Vec 𝕋 n) (b : Bool) : Bool :=
  (List.finRange n).all fun i =>
    le (Z.step_underapproximateCandidate s b i) (Z.step_underapproximateLower s b i)
      && le (Z.I_error.inf i) zero && le zero (Z.I_error.sup i)


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.underapproximate (Z : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z.h n) (s : Vec 𝕋 n) (b : Bool) :
    Option (Vec 𝕋 n) :=
  let p := Z.step_underapproximateCandidate s b
  if Z.containsPoint H p then some p else if Z.step_underapproximateExact s b then some p else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
