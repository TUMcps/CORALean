import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOuter

/-!
# What `PolyZonotope` instantiates

`ContSet` is not among them — `InflatedContSet` supplies it, which is what makes
this the same class the exact layer instantiates.

`Reduce` is here and is *computable*, where the exact layer's instance is not.
That is the one inversion in the whole layer: `Tuple.sort` needs a
`LinearOrder`, which no float type has lawfully, so the exact ranking is
noncomputable, while `sortPerm` asks its comparator for nothing and `le` on a
machine scalar answers it. Soundness never depended on the ranking —
`reduceBy_outer` holds at every partition — so the unconstrained comparator
costs precision and nothing else.

The instance bounds the count of *stored* columns rather than of distinct
monomials, the exact layer's `reduce` running `compact` first and this one not.
`Operations/Reduce` says why, and the reason inverts again: what stops a float
`compact` is arithmetic, not decidability.

`LinComb` is missing where the exact layer has it; it has no float counterpart
yet.

`quadMap` has no class to instantiate and gets none, as over ℝ: no other
representation computes it, and a class one representation implements is a name
rather than an interface. A caller that wants it names `PolyZonotope.quadMap`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

instance {n : ℕ} : Plus (PolyZonotope 𝕋 n) (Vec ℝ n) where
  plus := PolyZonotope.plus
  plus_outer := PolyZonotope.plus_outer

instance {n : ℕ} : Reduce (PolyZonotope 𝕋 n) (Vec ℝ n) where
  reduce := PolyZonotope.reduce
  reduce_outer := PolyZonotope.reduce_outer

instance : Mtimes (Mat 𝕋) (PolyZonotope 𝕋) where
  mtimes := PolyZonotope.mtimes
  mtimes_outer M PZ := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact PolyZonotope.mtimes_outer M PZ

end CORALean.Float
