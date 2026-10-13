import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexInCone
import CORALean.ContSet.PolyZonotope.Real.Operations.IsPolytopeCexCorners
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraAccepts

/-!
# CORA's `isPolytope` accepts a non-polytope

`PolyZonotope.coraAccepts` holds for `PolyZonotope.isPolytopeCex` and its four hull vertices,
so the `true` path of `isPolytope` [1] fires, though the set is not convex (FINDINGS.md).

## References

* [1] `contSet/@polyZonotope/isPolytope.m`, CORA (Sep. 2025), by N. Kochdumper (2019).
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

set_option simprocs false in
/-- Exponents: the first test of `isPolytope` does not fire. The vertex test: from each of the four
hull vertices the other three lie in the cone (`isPolytopeCex_coraAccepts`). -/
theorem PolyZonotope.isPolytopeCex_coraAccepts :
    PolyZonotope.isPolytopeCex.coraAccepts PolyZonotope.isPolytopeCexCorners := by -- --- PROOF ---
  refine ⟨fun i k => by fin_cases i <;> fin_cases k <;> decide, ?_⟩
  -- the difference of a corner image with itself is in the cone too (`0`), so `≠` is not used
  intro s t _
  fin_cases s <;> fin_cases t <;>
    (apply PolyZonotope.isPolytopeCex_inCone
     · intro i
       fin_cases i <;> simp [PolyZonotope.isPolytopeCexCorners]
     · norm_num [PolyZonotope.isPolytopeCexCorners, Matrix.cons_val_two, Matrix.head_cons,
         Matrix.tail_cons]
     · norm_num [PolyZonotope.isPolytopeCexCorners, Matrix.cons_val_two, Matrix.head_cons,
         Matrix.tail_cons])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
