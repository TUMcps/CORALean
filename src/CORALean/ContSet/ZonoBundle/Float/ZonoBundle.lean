import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# Zonotope bundles over a floating-point scalar: the representation

CORA's `zonoBundle` [1, §3.5.5] at float zonotopes: the family is stored and the
intersection is what it denotes, each member already inflated by its own error
box. So there is no `InflatedContSet` instance and `Instances` gives `ContSet`
directly — one ambient box cannot stand in for the members': `⋂ᵢ (Nᵢ + Eᵢ)` can
be nonempty where `⋂ᵢ Nᵢ` is empty, and no `E` then makes `(⋂ᵢ Nᵢ) + E` contain
it.

`GZonoBundle α` is indexed by the ambient type its members store, as the exact
layer's `ZonoBundle α` is, each member a `GZonotope α`, and what it denotes is the
intersection of the members' generic sets. `ZonoBundle 𝕋 n` is the vector case, a
reducible abbreviation, so the family `ZonoBundle 𝕋 : ℕ → Type` an algorithm is
generic over keeps its spelling, and its operations keep the names `ZonoBundle.*`.

`k = 0` denotes an intersection over an empty family, which is `univ` — the
whole space, not `∅` — exactly as over ℝ, and every degenerate case below is
read against that rather than against `Zonotope`'s.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure GZonoBundle (α : Type) where
  k : ℕ
  Z : Fin k → GZonotope α

abbrev ZonoBundle (𝕋 : Type) (n : ℕ) := GZonoBundle (Vec 𝕋 n)

/-- What the family denotes, at any ambient type: the intersection of the members'
own inflated sets, so the rounding each has paid for is already inside this. -/
def GZonoBundle.construct {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (zB : GZonoBundle α) : Set β :=
  ⋂ i, (zB.Z i).construct

/-- The generic set at `Vec`, spelled through the members' `Zonotope.construct` so
statements read locally; it is `GZonoBundle.construct` by definition. -/
def ZonoBundle.construct (zB : ZonoBundle 𝕋 n) : Set (Vec ℝ n) :=
  ⋂ i, Zonotope.construct (zB.Z i)

/-! ## Storage

A member's fields are function types and so is the family, so the bundle an
operation returns is a closure over the one it was given and a loop pays for its
whole history on every entry read. `materialise` stores the family and every
member in it; `materialise_eq` says it is the identity, which is what each proof
in `Instances` rewrites with, exactly as `Zonotope`'s does. -/

def ZonoBundle.materialise (zB : ZonoBundle 𝕋 n) : ZonoBundle 𝕋 n :=
  let Z : Vector (Zonotope 𝕋 n) zB.k := Vector.ofFn fun i => Zonotope.materialise (zB.Z i)
  { k := zB.k
    Z := fun i => Z[i.val]'i.isLt }

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] in
@[simp] theorem ZonoBundle.materialise_eq (zB : ZonoBundle 𝕋 n) : zB.materialise = zB := by
  simp [ZonoBundle.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
