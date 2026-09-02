import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact

/-!
# What `PolyZonotope` instantiates

Each obligation is a theorem from `Theorems`, the exact ones read in the `⊆`
direction.

`Plus` and `LinComb` sit at every ambient type rather than at `Vec`, unlike
`Zonotope`'s, which `reduce` pins down: nothing this representation computes
needs coordinates. `Mtimes` is the exception, since its whole point is moving
between dimensions.

`quadMap` has no class to instantiate and gets none: no other representation
here computes it, and a class one representation implements is a name, not an
interface. A caller that wants it names `PolyZonotope.quadMap`.

No `Reduce`. Order reduction here is not the zonotope's generator ranking: it
also has to merge equal exponent columns and drop the factors that fall out of
use, and an unreduced exponent matrix is what makes the bound on the order
meaningless. Left out rather than faked — a representation owes nothing it
cannot compute.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}

instance : ContSet (PolyZonotope α) α := ⟨PolyZonotope.construct⟩

instance : Plus (PolyZonotope α) α where
  plus := PolyZonotope.plus
  plus_outer PZ₁ PZ₂ := (PolyZonotope.plus_exact PZ₁ PZ₂).subset

noncomputable instance : LinComb (PolyZonotope α) α where
  linComb := PolyZonotope.linComb
  linComb_outer := PolyZonotope.linComb_outer

instance : Mtimes (Mat ℝ) (fun n => PolyZonotope (Vec ℝ n)) where
  mtimes := PolyZonotope.mtimes
  mtimes_outer M PZ := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (PolyZonotope.mtimes_exact M PZ).subset

end CORALean.Real
