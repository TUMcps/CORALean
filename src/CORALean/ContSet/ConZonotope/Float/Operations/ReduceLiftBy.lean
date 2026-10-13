import CORALean.ContSet.ConZonotope.Float.Operations.LiftEq
import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy

/-!
# `ConZonotope.reduceLiftBy` over a floating-point scalar

CORA's `@conZonotope/reduce` [1, Sec. 4.3] at a given partition, on the stored floats. The
lifted zonotope `liftEq` is reduced by the float `Zonotope.reduceBy`, whose diagonal block
rounds up, and its lower rows are read back as the equality system, the interval `bₑ` carried
over unchanged. The inequality rows follow the kept generators, zero on the fresh ones, with
the bound raised by the dropped generators' reach `radius` (the float `keepSlack`), rounded
up. The error box is the operand's: nothing is charged to it.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.reduceLiftBy (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- Z⁺ = [G; Aₑ], reduced at `part`
  let Zred := cZ.liftEq.reduceBy part
  -- the first `n` rows are the generators
  let Gnew : Fin Zred.h → Vec 𝕋 n := fun j k => Zred.G j (Fin.castAdd cZ.P.me k)
  -- the last `mₑ` rows are the equality system, `bₑ` unchanged
  let Anew : Fin cZ.P.me → Vec 𝕋 Zred.h := fun i j => Zred.G j (Fin.natAdd n i)
  -- each inequality row on the kept generators, zero on the fresh ones
  let Aineq : Fin cZ.P.m → Vec 𝕋 Zred.h := fun i =>
    Fin.append (fun l => cZ.P.A i (part.left l)) fun _ => zero
  -- what the dropped generators can add to a row, rounded up
  let slack : Vec 𝕋 cZ.P.m := radius fun i l => cZ.P.A i (part.right l)
  { h := Zred.h
    c := cZ.c
    G := Gnew
    P := { m := cZ.P.m, A := Aineq, b := fun i => addUp (cZ.P.b i) (slack i),
           me := cZ.P.me, Ae := Anew, be := cZ.P.be }
    E := cZ.E }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
