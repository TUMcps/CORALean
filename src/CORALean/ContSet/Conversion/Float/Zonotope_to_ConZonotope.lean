module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A zonotope as a constrained one, over a floating-point scalar

Nothing to satisfy, and nothing rounds: the fields are copied and the constraint
list is empty.

Not routed through the exact layer's version — the float `fullspace` reads as an
empty inequality block and an empty slab, which denotes everything but is not the
exact layer's `fullspace` term. Membership is the shorter argument anyway.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.conZonotope_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.conZonotope.construct := by
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx
  exact ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, HPolytope.mem_fullspace β, hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
