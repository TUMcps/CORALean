module

public import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingParallelotope
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceMethC

@[expose] public section

/-!
# `ZonoBundle.shrink`

CORA's `@zonoBundle/shrink` [1]: every member is reduced to order `1` by method C, the reduced
members are intersected (a polytope CORA builds with `and_`), and each member becomes the
parallelotope along its reduced edges that encloses the intersection (`enclosingParallelotope`).

Three differences, none changing what the result encloses. The box of `Γ⁻¹ P` is the intersection of
the reduced members' boxes, not the box of the polytope (a linear program); `methC` runs at its
default filter lengths; CORA returns `[]` for an empty polytope, here its parallelotopes enclose
nothing. The reduced member's edges are its first `n` generators, as `Γ`, padded by axes.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – the bundle has a member

## Output
* the bundle with each member reduced and enclosed

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
