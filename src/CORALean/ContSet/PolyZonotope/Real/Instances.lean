import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOuter

/-!
# What `PolyZonotope` instantiates

Each obligation is a theorem from `Theorems`, the exact ones read in the `⊆`
direction.

`Plus` and `LinComb` sit at every ambient type rather than at `Vec`: neither
needs coordinates. `Reduce` pins down `Vec`, as `Zonotope`'s does, since a
generator ranking and a box are both entrywise. `Mtimes` is the exception again,
its whole point being to move between dimensions.

`quadMap` has no class to instantiate and gets none: no other representation
here computes it, and a class one representation implements is a name, not an
interface. A caller that wants it names `PolyZonotope.quadMap`.

`Reduce` bounds the *dependent* generator count. That is what the class field
offers — one number — and what the independent block does under an order bound
is a second question `reduce` does not answer; the operation's docstring says
so.

Noncomputable, twice over: `compact` decides whether a generator of a real
module is zero, and the ranking orders reals.
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

noncomputable instance : Reduce (PolyZonotope (Vec ℝ n)) (Vec ℝ n) where
  reduce := PolyZonotope.reduce
  reduce_outer := PolyZonotope.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => PolyZonotope (Vec ℝ n)) where
  mtimes := PolyZonotope.mtimes
  mtimes_outer M PZ := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (PolyZonotope.mtimes_exact M PZ).subset

end CORALean.Real
