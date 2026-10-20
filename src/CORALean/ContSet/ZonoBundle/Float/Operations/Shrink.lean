module

public import CORALean.ContSet.ZonoBundle.Float.Operations.EnclosingParallelotope
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceMethC

@[expose] public section

/-!
# `ZonoBundle.shrink`, over a floating-point scalar

CORA's `@zonoBundle/shrink` [1]: every member is reduced to order `1` by method C, the reduced
members are intersected, and each member is replaced by the parallelotope along the reduced
member's own edges that encloses the intersection. The intersection is the bundle of the reduced
members; the parallelotope is `enclosingParallelotope`, its `Γ⁻¹` a checked candidate.

As at the exact layer: the box of `Γ⁻¹ P` is the intersection of the reduced members' boxes; the
empty case is not decided; the edges are the reduced member's first `n` generators, zeros where it
has fewer. Where its own check fails, the float `reduceMethC` returns a member unchanged.

## Inputs
* `zB` – float zonotope bundle

## Hypotheses
* `hk` – the bundle has a member

## Output
* the bundle with each member reduced and enclosed

## References

* [1] `contSet/@zonoBundle/shrink.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `shrink`: each member replaced by the parallelotope, along the edges of its `methC`
reduction to order `1`, around the intersection of those reductions. -/
def ZonoBundle.shrink (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) : ZonoBundle (Vec 𝕋 n) :=
  let Zred : Fin zB.k → Zonotope (Vec 𝕋 n) :=                     -- reduce(Z_i, 'methC', 1)
    fun i => Zonotope.reduceMethC (zB.Z i) 1
  let P : ZonoBundle (Vec 𝕋 n) := ⟨zB.k, Zred⟩                    -- `⋂ polytope(Zred_i)`
  ⟨zB.k, fun i =>
    P.enclosingParallelotope hk                              -- parallelotope(P, Zred_i.G)
      (fun r c => if hc : c.val < (Zred i).h then (Zred i).G ⟨c.val, hc⟩ r else zero)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
