import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

/-!
# `Zonotope.map` is exactly the image under a linear map

The same coefficients work in both directions — a linear map introduces no new
freedom and removes none — so linearity carried through the sum is the whole
proof. A linear image of a zonotope is a zonotope, which is what the propagation
loop rests on.

`mtimes_exact` is this at `A *ᵥ ·`. No `mtimes_outer` here: the float `mtimes`
pays its rounding into the error box, so it reproves this alongside the spill
rather than composing with it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

theorem Zonotope.map_exact (f : α →ₗ[ℝ] β) (Z : Zonotope α) :
    f '' Z.construct = (Z.map f).construct := by
  have hf : ∀ b : Fin Z.h → ℝ, f (Z.c + ∑ j, b j • Z.G j)
      = (Z.map f).c + ∑ j, b j • (Z.map f).G j := by
    intro b
    rw [map_add, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => map_smul f (b j) (Z.G j))
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, hf b⟩
  · rintro y ⟨b, hb, hy⟩
    refine ⟨Z.c + ∑ j, b j • Z.G j, ⟨b, hb, rfl⟩, ?_⟩
    rw [hy]
    exact hf b

theorem Zonotope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    (M *ᵥ ·) '' Z.construct = (Zonotope.mtimes M Z).construct :=
  Zonotope.map_exact (Matrix.mulVecLin M) Z

/-- What `LinMtimes` asks of `mapOf`: a set holding one map is that map. -/
theorem Zonotope.lmtimes_singleton_outer (f : α →ₗ[ℝ] β) (Z : Zonotope α) :
    (⋃ g ∈ ({f} : Set (α →ₗ[ℝ] β)), g '' Z.construct) ⊆ (Zonotope.mapOf f Z).construct := by
  refine Set.iUnion₂_subset fun g hg => ?_
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact (Zonotope.map_exact f Z).subset

/-- CORA's matZonotope times a matrix, exactly, from either side. Both are
`map_exact` at a different linear map — the whole of what the matrix case
needs. -/
theorem Zonotope.matMulLeft_exact {p q r : ℕ} (M : Mat ℝ p q) (Z : Zonotope (Mat ℝ q r)) :
    (M * ·) '' Z.construct = (Zonotope.mapOf (matMulLeft M) Z).construct :=
  Zonotope.map_exact (matMulLeft M) Z

theorem Zonotope.matMulRight_exact {p q r : ℕ} (M : Mat ℝ q r) (Z : Zonotope (Mat ℝ p q)) :
    (· * M) '' Z.construct = (Zonotope.mapOf (matMulRight M) Z).construct :=
  Zonotope.map_exact (matMulRight M) Z

end CORALean.Real
