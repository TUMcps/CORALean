import CORALean.ContSet.ConZonotope.Real.Operations.LiftEq
import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeepBy
import CORALean.ContSet.HPolytope.Real.Operations.Eqs
import CORALean.ContSet.HPolytope.Real.Operations.Intersection

/-!
# `ConZonotope.reduceLiftBy`

CORA's `@conZonotope/reduce` [1, Sec. 4.3] at a given partition of the generators. The
equality rows `Aₑ β = bₑ` are lifted with the generators to the zonotope `[G; Aₑ]` with
centre `[c; -bₑ]` (`liftEq`), that zonotope is reduced by `reduceBy`'s box, and the lower
rows of the result are read back as the new equality system, `bₑ` unchanged because the
reduction keeps the centre. The boxed coefficients therefore enter the equalities through
the diagonal block, as in CORA, and an equality survives as a relaxed row rather than
being given up.

CORA's representation has no inequalities; this one does, and they are handled as
`reduceKeepBy` handles every row: each is read at the kept coefficients and loosened by what
the dropped ones can add (`keepRows`), the fresh box coefficients being unconstrained. Both
parts are outer, so the result is.

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

namespace CORALean.Real

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Reduce the lifted zonotope `[G; Aₑ]` at `part` and read the equality rows back off it;
the inequality rows follow the kept generators with their dropped slack. -/
noncomputable def ConZonotope.reduceLiftBy (cZ : ConZonotope (Vec ℝ n))
    (part : Split (Fin cZ.h) into (Fin q) ⊕ (Fin r)) : ConZonotope (Vec ℝ n) :=
  -- Z⁺ = {[G; Aₑ], [c; -bₑ]} with the inequality rows of `P`
  let Zup := cZ.liftEq
  -- the lifted zonotope, reduced; the centre is untouched, the box lives in the new columns
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
