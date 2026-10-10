import CORALean.ContSet.Polygon.Real.Operations.Subtract
import CORALean.ContSet.Polygon.Real.Theorems.IsCompact

/-!
# `Polygon.subtract` encloses the set difference and stays in the minuend

For a minuend that is the closure of its interior (a `polyshape` is), the regularized difference
contains the set difference `P₁ \ P₂`, lies in `P₁`, and avoids the interior of `P₂`. The first
needs `P₂` closed (`Polygon.isCompact_construct`): a point outside `P₂` has a neighbourhood
outside it, which meets the interior of `P₁`. It is an outer statement for the set difference;
the result is larger than it only by boundary points of `P₂`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.subtract_outer (P₁ P₂ : Polygon)
    (hreg : ContSet.construct P₁ = closure (interior (ContSet.construct P₁))) :
    ContSet.construct P₁ \ ContSet.construct P₂ ⊆ Polygon.subtract P₁ P₂ ∧
      Polygon.subtract P₁ P₂ ⊆ ContSet.construct P₁ ∧
      Polygon.subtract P₁ P₂ ∩ interior (ContSet.construct P₂) = ∅ := by -- --- PROOF ---
  have hcl₁ : IsClosed (ContSet.construct P₁) := (Polygon.isCompact_construct P₁).isClosed
  have hcl₂ : IsClosed (ContSet.construct P₂) := (Polygon.isCompact_construct P₂).isClosed
  refine ⟨?_, ?_, ?_⟩
  · -- a point outside `P₂` has an open neighbourhood outside it, meeting `interior P₁`
    rintro x ⟨hx₁, hx₂⟩
    rw [Polygon.subtract, mem_closure_iff]
    intro U hU hxU
    have hx₁' := hreg ▸ hx₁
    obtain ⟨y, hyU, hy⟩ := mem_closure_iff.mp hx₁' (U ∩ (ContSet.construct P₂)ᶜ)
      (hU.inter hcl₂.isOpen_compl) ⟨hxU, hx₂⟩
    exact ⟨y, hyU.1, hy, hyU.2⟩
  · exact closure_minimal (fun y hy => interior_subset hy.1) hcl₁
  · -- the difference lies in the closure of the complement of `P₂`
    refine Set.eq_empty_of_forall_notMem ?_
    rintro x ⟨hx, hxi⟩
    have hx' : x ∈ closure ((ContSet.construct P₂)ᶜ) :=
      closure_mono (fun y hy => hy.2) hx
    obtain ⟨y, hy, hy'⟩ := mem_closure_iff.mp hx' _ isOpen_interior hxi
    exact hy' (interior_subset hy)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
