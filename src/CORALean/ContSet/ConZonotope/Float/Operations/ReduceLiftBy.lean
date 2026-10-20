module

public import CORALean.ContSet.ConZonotope.Float.Operations.LiftEq
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.EqsWithin
public import CORALean.ContSet.HPolytope.Float.Operations.KeepCols
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy

@[expose] public section

/-!
# `ConZonotope.reduceLiftBy` over a floating-point scalar

CORA's `@conZonotope/reduce` [1, Sec. 4.3] at a given partition, on the stored floats. The
lifted zonotope `liftEq` is reduced by the float `Zonotope.reduceBy`, whose diagonal block
rounds up, and its lower rows are read back as the equality system, the right-hand side `bₑ`
carried over unchanged with its slack (`HPolytope.eqsWithin`). The inequality rows are the
constraint's own operations: `HPolytope.keepCols` keeps the kept generators' columns and writes
the dropped generators' reach into each row's slack (#218), `dropEqs` leaves the equalities to the
lifted zonotope, and `padLeft` puts zeros at the fresh generators. The error box is the operand's:
nothing is charged to it.

## Inputs
* `cZ` – float constrained zonotope
* `part` – generator partition

## Output
* enclosing constrained zonotope reduced along the partition

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


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
  { h := Zred.h
    c := cZ.c
    G := Gnew
    -- the inequality rows on the kept generators, zero on the fresh ones; the equalities read back
    P := (((cZ.P.keepCols part).dropEqs).padLeft (n + cZ.P.me)).stackRows
      (HPolytope.eqsWithin Anew cZ.P.be cZ.P.be_error)
    I_error := cZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
