import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

/-!
# A zonotope as a constrained one, over a floating-point scalar

Nothing to satisfy, and nothing rounds: the fields are copied and the constraint
list is empty.

Not routed through the exact layer's version — the float `fullspace` reads as an
empty inequality block and an empty slab, which denotes everything but is not the
exact layer's `fullspace` term. Membership is the shorter argument anyway.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Zonotope.conZonotope (Z : Zonotope 𝕋 n) : ConZonotope 𝕋 n :=
  ⟨Z.h, Z.c, Z.G, HPolytope.fullspace 𝕋 Z.h, Z.E⟩

variable [SoundFloatArithmetic 𝕋]

theorem Zonotope.conZonotope_outer (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ Z.conZonotope.construct := by
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx
  exact ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, HPolytope.mem_fullspace β, hx⟩

end CORALean.Float
