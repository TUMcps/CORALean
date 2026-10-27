module

public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeVPolytopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeExistsPolyZonotopeExact

@[expose] public section

/-!
# Every constrained zonotope is a polynomial zonotope

A nonempty constrained zonotope is a bounded polytope, the vertices of its coefficient domain
carried through the generators (`ConZonotope.vPolytope_exact`), and a bounded polytope is a
polynomial zonotope (`VPolytope.exists_polyZonotope_exact`, [1, Thm. 1]). Composing the two gives
the arrow of [1, Fig. 1 (Polytopes → Polynomial Zonotopes)] from the constrained zonotopes
exactly, not merely as the enclosure `ConZonotope.polyZonotope_contains`. Existence, as the polytope
step states it. A polynomial zonotope is never empty, so the empty constrained zonotope (infeasible
constraints) has no polynomial zonotope: the hypothesis is needed.

## Inputs
* `cZ` – constrained zonotope

## Hypotheses
* `hne` – set is nonempty

## Conclusion
* some polynomial zonotope equals the set

## References

* [1] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.exists_polyZonotope_exact (cZ : ConZonotope α)
    (hne : cZ.construct.Nonempty) : -- --- CONCL ---
    ∃ pZ : PolyZonotope α, pZ.construct = cZ.construct := by -- --- PROOF ---
  -- a point of the set comes from a point of the coefficient domain
  have hdom : cZ.domain.construct.Nonempty := by
    obtain ⟨x, β, hβ, hP, -⟩ := hne
    exact ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hβ, hP⟩⟩
  have hV := cZ.vPolytope_exact hdom
  -- the vertex list is not empty, its hull being
  have hk : 0 < (cZ.vPolytope hdom).k := by
    by_contra h
    have hk0 : (cZ.vPolytope hdom).k = 0 := by omega
    obtain ⟨x, hx⟩ := hne
    rw [← hV, VPolytope.construct_eq_convexHull] at hx
    have hrange : Set.range (cZ.vPolytope hdom).V = ∅ := by
      haveI : IsEmpty (Fin (cZ.vPolytope hdom).k) := by rw [hk0]; infer_instance
      exact Set.range_eq_empty _
    rw [hrange, convexHull_empty] at hx
    exact hx
  obtain ⟨pZ, hpZ⟩ := VPolytope.exists_polyZonotope_exact _ hk
  exact ⟨pZ, hpZ.trans hV⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
