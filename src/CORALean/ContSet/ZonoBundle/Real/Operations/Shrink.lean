module

public import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingParallelotope
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceMethC

@[expose] public section

/-!
# `ZonoBundle.shrink`

CORA's `@zonoBundle/shrink` [1]: every member is reduced to order `1` by method C, the reduced
members are intersected, and each member is replaced by the parallelotope along the reduced
member's own edges that encloses the intersection. The intersection is the bundle of the reduced
members, a polytope CORA builds with `and_`; the parallelotope is `enclosingParallelotope`.

Three differences, none changing what the result encloses. The box of `Γ⁻¹ P` is the intersection
of the reduced members' boxes, where CORA wants the box of the polytope itself (a linear program).
`methC` runs at its default filter lengths, CORA's `filterLength` argument being a tuning of that
search. CORA returns `[]` when the polytope is empty; the bundle of an empty intersection is not
decided here, and its parallelotopes enclose nothing. The reduced member's edges are its first `n`
generators, as `Γ`; at fewer, zeros, which `enclosingParallelotope` replaces by the axes.

## References

* [1] `contSet/@zonoBundle/shrink.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `shrink`: each member replaced by the parallelotope, along the edges of its `methC`
reduction to order `1`, around the intersection of those reductions. -/
noncomputable def ZonoBundle.shrink (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ZonoBundle (Vec ℝ n) :=
  let Zred : Fin zB.k → Zonotope (Vec ℝ n) :=               -- reduce(Z_i, 'methC', 1)
    fun i => (zB.Z i).reduceMethC 1
  let P : ZonoBundle (Vec ℝ n) := ⟨zB.k, Zred⟩              -- `⋂ polytope(Zred_i)`
  ⟨zB.k, fun i =>
    P.enclosingParallelotope hk                                   -- parallelotope(P, Zred_i.G)
      (Matrix.of fun r c => if hc : c.1 < (Zred i).h then (Zred i).G ⟨c.1, hc⟩ r else 0)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
