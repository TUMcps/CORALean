module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitMany
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `PolyZonotope.containsPointSet`

CORA's `@polyZonotope/containsPointSet`, "checks if a point set is fully enclosed by a tight
over-approximation of a polynomial zonotope": split the polynomial zonotope `splits` times along
its longest generator (`2^splits` pieces), enclose each piece by a Girard-reduced zonotope
converted to a polytope, and report whether every point lies in at least one of these polytopes.

The union of the pieces' polytopes is the tight over-approximation. CORA's code then appends the
reduced zonotope of the whole set to the list (`qZsplit{end}`), and a point in that polytope is
accepted: that is the loose enclosure the splitting exists to avoid, and a point only it contains
is not in the tight one. It is not formalized; the row of `containsPointSet` in
`references/coverage/contSet/polyZonotope.md` records the difference.

It is a test of one side only. A point outside every enclosure is outside the set, so `false`
decides non-containment; a point inside an enclosure may still be outside the set, so
`true` decides nothing. The tight enclosure also makes `false` sharper than CORA's. CORA tests
membership with `contains_(·,'approx',1e-10)`, which accepts more than the polytope does; the
definition here is the exact membership, and what is proved holds for CORA's a fortiori.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every point lies in the polytope of the reduced zonotope of some piece. -/
noncomputable def PolyZonotope.containsPointSet (pZ : PolyZonotope (Vec ℝ n)) {N : ℕ}
    (points : Fin N → Vec ℝ n) (splits order : ℕ) : Prop :=
  let pZsplit := pZ.splitMany splits
  -- `polytope(reduce(zonotope(·), 'girard', order))`, one per piece
  let qZsplit : List (Set (Vec ℝ n)) :=
    pZsplit.map (fun q => (q.zonotopeEven.reduceGirard order).vPolytope.construct)
  ∀ i, ∃ Q ∈ qZsplit, points i ∈ Q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
