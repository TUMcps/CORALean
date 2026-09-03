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

`Reduce`'s one number bounds both generator blocks together, which is what the
class field's `o` means everywhere else too. `reduce_order_le` states it; the
class carries only the enclosure, since a representation whose order is read
differently — a zonotope's, an interval's — still instantiates the same field.

Noncomputable, twice over: `compact` decides whether a generator of a real
module is zero, and the ranking orders reals.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-September-2026
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

/-- The polynomial-zonotope family over vectors. A generic theorem quantifies
over `S : ℕ → Type` and the elaborator cannot read that family off one member, so a
use site has to name it: `(S := 𝒫𝒵)`. Two letters, `𝒫` alone being Mathlib's
powerset. -/
scoped notation "𝒫𝒵" => fun n => PolyZonotope (Vec ℝ n)

end CORALean.Real
