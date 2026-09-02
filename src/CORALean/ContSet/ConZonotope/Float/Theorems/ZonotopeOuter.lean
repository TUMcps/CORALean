import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.ConZonotope.Float.Operations.Zonotope

/-!
# Forgetting the constraints encloses, adding none loses nothing

Both boxes are the same box, so `mono_subset` reduces each direction to its
exact-layer counterpart and there is no rounding to account for.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem ConZonotope.zonotope_outer (C : ConZonotope 𝕋 n) :
    C.construct ⊆ C.zonotope.construct :=
  mono_subset (Real.ConZonotope.zonotope_outer (nominal C)) subset_rfl

/-- Not routed through the exact layer's version: the float `fullspace` reads as
an empty inequality block and an empty slab, which denotes everything but is not
the exact layer's `fullspace` term. Membership is the shorter argument anyway. -/
theorem Zonotope.conZonotope_outer (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ Z.conZonotope.construct := by
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx
  exact ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, HPolytope.mem_fullspace β, hx⟩

end CORALean.Float
