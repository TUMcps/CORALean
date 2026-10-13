module

public import CORALean.ContSet.Polygon.Real.Operations.LinComb
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# `Polygon.linComb` encloses the segments

Every segment between a point of one polygon and a point of the other lies in the segment set of
some pair of pieces, which the pair's `VPolytope.linComb` encloses.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.linComb_outer (P Q : Polygon) :
    segments (ContSet.construct P) (ContSet.construct Q) ⊆
      ContSet.construct (Polygon.linComb P Q) := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩
  obtain ⟨p, hp, hy₁⟩ := SetUnion.mem_construct.mp hy₁
  obtain ⟨q, hq, hy₂⟩ := SetUnion.mem_construct.mp hy₂
  refine SetUnion.mem_construct.mpr ⟨VPolytope.linComb p q, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(p, q), List.mem_product.mpr ⟨hp, hq⟩, rfl⟩
  · exact VPolytope.linComb_outer p q ⟨y₁, hy₁, y₂, hy₂, lam, hlam, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
