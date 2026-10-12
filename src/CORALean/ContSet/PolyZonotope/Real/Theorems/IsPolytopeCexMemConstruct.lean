import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexCoraVertex

/-!
# The set of `isPolytopeCex`

`isPolytopeCex.construct` is the map `(a, b, c) ↦ (2a + b, a c)` on the factor cube.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is the corner-image map applied to the factor cube. -/
theorem PolyZonotope.isPolytopeCex_mem_construct (x : Vec ℝ 2) :
    x ∈ PolyZonotope.isPolytopeCex.construct ↔
      ∃ a : Fin 3 → ℝ, (∀ k, |a k| ≤ 1) ∧ x = ![2 * a 0 + a 1, a 0 * a 2] := by -- --- PROOF ---
  have hz : ∀ β : Fin PolyZonotope.isPolytopeCex.q → ℝ,
      ∑ j, β j • PolyZonotope.isPolytopeCex.GI j = 0 :=
    fun β => Finset.sum_eq_zero (fun j _ => Fin.elim0 j)
  constructor
  · rintro ⟨a, β, ha, -, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [← PolyZonotope.isPolytopeCex_coraVertex]
    rw [hx, hz, add_zero]
    rfl
  · rintro ⟨a, ha, hx⟩
    refine ⟨a, fun j => Fin.elim0 j, ha, fun j => Fin.elim0 j, ?_⟩
    rw [hx, ← PolyZonotope.isPolytopeCex_coraVertex, hz, add_zero]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
