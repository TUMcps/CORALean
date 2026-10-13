import CORALean.ContSet.ZonoBundle.Real.Operations.EnclosingParallelotope
import CORALean.ContSet.Zonotope.Real.Operations.MethCBasis

/-!
# `ZonoBundle.reduceCombined`

CORA's `@zonoBundle/reduceCombined(zB, 'methC')`: the bundle reduced as a whole, to one
zonotope, rather than member by member. `priv_reduceMethC` [1] stacks the generators of every
member, selects `n` of them by the length and volume filters of method C, and returns the
parallelotope along them around the bundle: the selected edges `Γ`, then `Γ box(Γ⁻¹ Z_∩)`, which
is `enclosingParallelotope`. The result is a zonotope, not a bundle, whatever the documentation
says.

The selection is `Zonotope.methCBasis` at the stacked generators, every one a candidate: its
`rem = 1` path of the filters, as for `Zonotope.reduceMethC`. CORA's own scaling `W` cancels,
as there. `order`, which CORA's `reduceCombined` takes and never reads, and `filterLength`, the
tuning of the filters, are not arguments.

## References

* [1] `contSet/@zonoBundle/reduceCombined.m` and `private/priv_reduceMethC.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduceCombined(zB, 'methC')`: the parallelotope along the `methC`-selected generators
of all members, around the bundle. -/
noncomputable def ZonoBundle.reduceCombined (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    Zonotope (Vec ℝ n) :=
  let e := finSigmaFinEquiv (m := zB.k) (n := fun i => (zB.Z i).h)  -- (member, generator) ≃ index
  let Zall : Zonotope (Vec ℝ n) :=                                 -- the generators of all members
    ⟨∑ i, (zB.Z i).h, 0, fun j => (zB.Z (e.symm j).1).G (e.symm j).2⟩
  let part := (Partition.split 0 Zall.h).reindex                   -- every generator a candidate
    (finCongr (zero_add Zall.h).symm)
  zB.enclosingParallelotope hk (Zall.methCBasis part)             -- `Γ box(Γ⁻¹ Z_∩)`

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
