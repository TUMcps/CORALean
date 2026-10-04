import CORALean.ContSet.PolyZonotope.Real.Operations.SplitMany
import CORALean.ContSet.PolyZonotope.Real.Operations.ZonotopeCora
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# `PolyZonotope.containsPointSet`

CORA's `@polyZonotope/containsPointSet`: split the polynomial zonotope `splits` times along
its longest generator (`2^splits` pieces), enclose each piece, and the whole set, by a
Girard-reduced zonotope converted to a polytope, and report whether every point lies in
at least one of these polytopes.

It is a test of one side only. A point outside every enclosure is outside the set, so `false`
decides non-containment; a point inside an enclosure may still be outside the set, so
`true` decides nothing. CORA tests membership with `contains_(·,'approx',1e-10)`, which
accepts more than the polytope does; the definition here is the exact membership, and what
is proved holds for CORA's a fortiori.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every point lies in the polytope of the reduced zonotope of some piece, or of the set. -/
noncomputable def PolyZonotope.containsPointSet (pZ : PolyZonotope (Vec ℝ n)) {N : ℕ}
    (points : Fin N → Vec ℝ n) (splits order : ℕ) : Prop :=
  let pZsplit := pZ.splitMany splits
  -- `polytope(reduce(zonotope(·), 'girard', order))`, one per piece and one for `pZ`
  let qZsplit : List (Set (Vec ℝ n)) :=
    pZsplit.map (fun q => (q.zonotopeCora.reduceGirard order).vPolytope.construct)
      ++ [(pZ.zonotopeCora.reduceGirard order).vPolytope.construct]
  ∀ i, ∃ Q ∈ qZsplit, points i ∈ Q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
