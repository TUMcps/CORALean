import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal

/-!
# One signed row of [1, Thm. 3], indexed by a generator subset

The normal of the row `(b, T)`: the cross product of the `n + 1` generators `T` selects, taken in
increasing order, with the sign `b` — `true` is `+`, `false` is `-`. This is the `Bool × Finset
(Fin Z.h)` indexing of the printed `C`'s `2·C(p, n-1)` rows that `Zonotope.gen_removable_iff` counts
over, where `Zonotope.facetNormal` is indexed by [1, Thm. 2]'s own selections `Fin n → Fin Z.h`. A
subset of the wrong size has no normal, and gets `0`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The normal of the signed row `(b, T)`: `±` the cross product of the generators `T` selects, in
increasing order. -/
noncomputable def Zonotope.minkDiffRowNormal {n : ℕ} (Z : Zonotope (Vec ℝ (n + 2)))
    (j : Bool × Finset (Fin Z.h)) : Vec ℝ (n + 2) :=
  if h : j.2.card = n + 1 then
    (if j.1 then (1 : ℝ) else -1) • Z.facetNormal (j.2.orderEmbOfFin h)
  else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
