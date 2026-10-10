import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.underapproximateCandidate`, over a floating-point scalar

The float candidate for CORA's `@zonotope/underapproximate(Z, S)` vertex `c ± Σⱼ sign(sᵀ gⱼ) gⱼ`
in direction `s`, one named `let` per step of `Real.Zonotope.underapproximate`. Rounding may move
it off the vertex, so it is not trusted: `Zonotope.underapproximate` returns it only once
`Zonotope.containsPoint` certifies it inside the zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The candidate vertex for direction `s`; rounding may move it, `underapproximate` checks it. -/
def Zonotope.underapproximateCandidate (Z : Zonotope 𝕋 n) (s : Vec 𝕋 n) (b : Bool) : Vec 𝕋 n :=
  let d := fun j : Fin Z.h => sumUp fun i => mulUp (s i) (Z.G j i)  -- sᵀ gⱼ
  let sgn := fun j : Fin Z.h =>  -- sign(sᵀ gⱼ), `0` unless strictly signed, flipped for `false`
    if le (d j) zero then (if le zero (d j) then zero else if b then neg one else one)
    else (if b then one else neg one)
  fun i => addUp (Z.c i) (sumUp fun j => mulUp (sgn j) (Z.G j i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
