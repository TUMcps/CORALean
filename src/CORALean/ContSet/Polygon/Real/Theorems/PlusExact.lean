import CORALean.ContSet.Polygon.Real.Operations.Plus

/-!
# `Polygon.plus` is the Minkowski sum

Exactly: a sum of two unions is the union of the pairwise sums, and each pairwise sum is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

open Pointwise in
theorem Polygon.plus_exact (P Q : Polygon) :
    ContSet.construct P + ContSet.construct Q =
      ContSet.construct (Polygon.plus P Q) := by -- --- PROOF ---
  refine Set.Subset.antisymm (SetUnion.plus_outer P Q) ?_
  intro x hx
  obtain ⟨t, ht, hx⟩ := SetUnion.mem_construct.mp hx
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hp, hq⟩ := List.mem_product.mp hpq
  have hx' : x ∈ VPolytope.construct (VPolytope.plus p q) := hx
  rw [← VPolytope.plus_exact] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, SetUnion.mem_construct.mpr ⟨p, hp, ha⟩, b,
    SetUnion.mem_construct.mpr ⟨q, hq, hb⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
