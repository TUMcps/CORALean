module

public import CORALean.ContSet.ConZonotope.Real.Operations.LiftEq
public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeepBy
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Intersection

@[expose] public section

/-!
# `ConZonotope.reduceLiftBy`

CORA's `@conZonotope/reduce` [1, Sec. 4.3] at a given partition of the generators. The equality rows
`Aₑ β = bₑ` are lifted with the generators to the zonotope `[G; Aₑ]` with center `[c; -bₑ]`
(`liftEq`), that zonotope is reduced by `reduceBy`'s box, and the lower rows of the result are read
back as the new equality system, `bₑ` unchanged because the reduction keeps the center.

CORA's representation has no inequalities; this one does, and they are handled as `reduceKeepBy`
handles every row: read at the kept coefficients and loosened by what the dropped ones can add
(`keepRows`), the fresh box coefficients unconstrained. Both parts are outer, so the result is.

## Inputs
* `cZ` – constrained zonotope
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
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Reduce the lifted zonotope `[G; Aₑ]` at `part` and read the equality rows back off it. Not the
polytope's work (data): `bₑ` carried to the equality rows read back (`HPolytope.eqs`); the
inequality rows are `keepRows`'s. -/
noncomputable def ConZonotope.reduceLiftBy (cZ : ConZonotope (Vec ℝ n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) : ConZonotope (Vec ℝ n) :=
  -- Z⁺ = {[G; Aₑ], [c; -bₑ]} with the inequality rows of `P`
  let Zup := cZ.liftEq
  -- the lifted zonotope, reduced; the center is untouched, the box lives in the new columns
  let Zred := Zup.reduceKeepBy part
  -- the first `n` rows are the generators
  let Gnew : Fin Zred.h → Vec ℝ n := fun j k => Zred.G j (Fin.castAdd cZ.P.me k)
  -- the last `mₑ` rows are the equality system `Aₑ`, with `bₑ` unchanged
  let Anew : Mat ℝ cZ.P.me Zred.h := fun i j => Zred.G j (Fin.natAdd n i)
  { h := Zred.h
    c := cZ.c
    G := Gnew
    P := Zred.P.intersection (HPolytope.eqs Anew cZ.P.be) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
