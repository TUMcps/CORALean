import CORALean.ContSet.ZonoBundle.Float.Operations.EnclosingParallelotope
import CORALean.ContSet.Zonotope.Float.Operations.MethCBasis

/-!
# `ZonoBundle.reduceCombined`, over a floating-point scalar

CORA's `@zonoBundle/reduceCombined(zB, 'methC')` [1]: the generators of every member stacked,
`n` of them selected as the basis `Γ`, and the parallelotope `Γ box(Γ⁻¹ Z_∩)` along them around
the bundle, which is `enclosingParallelotope`. The result is one zonotope, as CORA's code returns.

The selection is the float `Zonotope.methCBasis` at the stacked generators, the `n` longest,
where the exact layer runs method C's filters; which basis is taken costs precision alone, as
`enclosingParallelotope_outer` holds at any. `order` and `filterLength` are not arguments, as at
the exact layer.

## References

* [1] `contSet/@zonoBundle/reduceCombined.m` and `private/priv_reduceMethC.m`, CORA (Sep. 2025).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduceCombined(zB, 'methC')`: the parallelotope along `n` of the generators of all
members, around the bundle. -/
def ZonoBundle.reduceCombined (zB : ZonoBundle 𝕋 n) (hk : 0 < zB.k) : Zonotope 𝕋 n :=
  let e := finSigmaFinEquiv (m := zB.k) (n := fun i => (zB.Z i).h)  -- (member, generator) ≃ index
  let Zall : Zonotope 𝕋 n :=                                        -- the generators of all members
    ⟨∑ i, (zB.Z i).h, fun _ => zero, fun j => (zB.Z (e.symm j).1).G (e.symm j).2,
     ⟨fun _ => zero, fun _ => zero⟩⟩
  zB.enclosingParallelotope hk Zall.methCBasis                      -- `Γ box(Γ⁻¹ Z_∩)`

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
