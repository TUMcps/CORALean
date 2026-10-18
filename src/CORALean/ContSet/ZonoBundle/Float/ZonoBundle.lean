module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# Zonotope bundles over a floating-point scalar: the representation

CORA's `zonoBundle` [1, §3.5.5] at float zonotopes: the family is stored and the
intersection is what it denotes, each member already inflated by its own error
box. So there is no `InflatedContSet` instance and `Instances` gives `ContSet`
directly — one ambient box cannot stand in for the members': `⋂ᵢ (Nᵢ + Eᵢ)` can be nonempty
where `⋂ᵢ Nᵢ` is empty, and no `E` then makes `(⋂ᵢ Nᵢ) + E` contain it.

`ZonoBundle α` is indexed by the ambient type its members store, as the exact
layer's `ZonoBundle α` is, each member a `Zonotope α`, and what it denotes is the
general `SetIntersection` of the members' generic sets (`toSetIntersection`), by definition,
so the facts of every intersection come from that class. The vector case is
`ZonoBundle (Vec 𝕋 n)`, and an algorithm generic over the dimension takes the
family `fun k => ZonoBundle (Vec 𝕋 k)`.

`k = 0` denotes an intersection over an empty family, which is `univ` — the
whole space, not `∅` — exactly as over ℝ, and every degenerate case below is
read against that rather than against `Zonotope`'s.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   18-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

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
