module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitMany
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `PolyZonotope.containsPointSet`

CORA's `@polyZonotope/containsPointSet`, "checks if a point set is fully enclosed by a tight
over-approximation of a polynomial zonotope": split the polynomial zonotope `splits` times
along its longest generator, enclose each piece by a Girard-reduced zonotope converted to a
polytope, and report whether every point lies in one of these polytopes. CORA's code then
appends the reduced zonotope of the whole set (`qZsplit{end}`); that loose enclosure is not
formalized (see `references/coverage/contSet/polyZonotope.md`). A point outside every enclosure is
outside the set, so `false` decides non-containment; `true` decides nothing. CORA tests with
`contains_(·,'approx',1e-10)`; here membership is exact, so what is proved holds for CORA's.

## Inputs
* `pZ` – polynomial zonotope
* `N` – number of points
* `points` – the points
* `splits` – number of splits
* `order` – zonotope reduction order

## Output
* Prop that every point lies in one of the split pieces' enclosures
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
