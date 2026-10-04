import CORALean.Global.Float.InverseTrig

/-!
# `Interval.atan2Lo`: `atan2` at a corner, from below

A lower bound of `atan2(b, a)`, the argument of `a + b i`, at floats `a`, `b`. In the right
half-plane it is `arctan (b / a)`, in the upper one `π/2 - arctan (a / b)`, in the lower one `-π/2
- arctan (a / b)`, each half-plane certified by `ltStrict`; elsewhere it is `-π`. `π/2` is `arccos
0`, its bounds from `acosDown`, `acosUp`; every end rounds down.
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

def Interval.atan2Lo (p k : ℕ) (a b : 𝕋) : 𝕋 :=
  -- `π/2` from above and below
  let hp := acosUp p k zero
  let hm := acosDown p k zero
  if ltStrict zero a = true then atanDown p k (divDown b a)
  else if ltStrict zero b = true then subDown hm (atanUp p k (divUp a b))
  else if ltStrict b zero = true then subDown (neg hp) (atanUp p k (divUp (neg a) (neg b)))
  else neg (addUp hp hp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
