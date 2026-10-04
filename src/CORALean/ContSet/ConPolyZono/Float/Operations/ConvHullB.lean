import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.RepVec
import CORALean.Global.Float.IntRound

/-!
# `ConPolyZono.convHullB`

The constraint bound of [1, Prop. 9]: the linear combination's, once per copy, and `1 - a`
for the weight row. The copies' bounds are copied; `1 - a` is an integer, enclosed by `intDown` and
`intUp`, so the weight row's interval only ever widens.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
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

/-- One copy of `b` per block, then the weight row's `1 - a`, rounded outward. -/
def ConPolyZono.convHullB (a : ℕ) {m : ℕ} (b : Interval (Vec 𝕋 m)) :
    Interval (Vec 𝕋 (a * m + 1)) :=
  ⟨Fin.append (Real.ConPolyZono.repVec a b.inf) (fun _ => intDown (1 - (a : ℤ))),
    Fin.append (Real.ConPolyZono.repVec a b.sup) (fun _ => intUp (1 - (a : ℤ)))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
