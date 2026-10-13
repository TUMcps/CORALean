module

public import CORALean.ContSet.Polygon.Float.Operations.LinComb
public import CORALean.ContSet.VPolytope.Float.Theorems.LinCombOuter

@[expose] public section

/-!
# `Polygon.linComb` encloses the segments

Pair by pair (`VPolytope.linComb_outer`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.linComb_outer (P Q : Polygon 𝕋) :
    segments (ContSet.construct P) (ContSet.construct Q) ⊆
      ContSet.construct (Polygon.linComb P Q) := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  obtain ⟨p, hp, hy₁⟩ := SetUnion.mem_construct.mp hy₁
  obtain ⟨q, hq, hy₂⟩ := SetUnion.mem_construct.mp hy₂
  refine SetUnion.mem_construct.mpr
    ⟨_, List.mem_map.mpr ⟨(p, q), List.mem_product.mpr ⟨hp, hq⟩, rfl⟩, ?_⟩
  have := VPolytope.linComb_outer p q ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  rwa [← VPolytope.materialise_eq (VPolytope.linComb p q)] at this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
