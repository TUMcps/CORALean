module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# Zonotope bundles over a floating-point scalar: the representation

CORA's `zonoBundle` [1, Def. 4] at float zonotopes: the family is stored and the intersection is
what it denotes, each member already inflated by its own error box. So there is no `InflatedContSet`
instance and `Instances` gives `ContSet` directly: `⋂ᵢ (Nᵢ + Eᵢ)` can be nonempty where `⋂ᵢ Nᵢ` is
empty, and no single `E` then makes `(⋂ᵢ Nᵢ) + E` contain it. `ZonoBundle α` is indexed by the
ambient type its members store, as the exact layer's is, and denotes the general `SetIntersection`
of its members (`toSetIntersection`), so the facts of every intersection come from that class.
`k = 0` denotes `univ`, the whole space and not `∅`, exactly as over ℝ.
There is no `I_error` and no `absorbRounding`: each member carries its own box.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   18-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A zonotope bundle over floats: `k` zonotopes, denoting their intersection. -/
structure ZonoBundle (α : Type) where
  k : ℕ
  Z : Fin k → Zonotope α

/-- The bundle as the general intersection of its members, listed in CORA's order. -/
def ZonoBundle.toSetIntersection {α : Type} (zB : ZonoBundle α) : SetIntersection (Zonotope α) :=
  ⟨List.ofFn zB.Z⟩

/-- What the family denotes, at any ambient type: the `SetIntersection` of the members'
own inflated sets, so the rounding each has paid for is already inside this. -/
def ZonoBundle.construct {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (zB : ZonoBundle α) : Set β :=
  ContSet.construct zB.toSetIntersection

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
