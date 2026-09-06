import CORALean.ContSet.ConPolyZono.Real.Operations.CompactCons
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecEqSum
import CORALean.ContSet.ConPolyZono.Real.Operations.ConsCol
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsCongr
import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMem
import CORALean.ContSet.PolyZonotope.Real.Operations.SumCompactKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.SumMonomialMerge

/-!
# Merging equal constraint exponent columns loses nothing

`compactCons` leaves the generators alone and moves only `A μ(α)`, which
`holds_congr` is exactly the statement about, so the point equation is the same
term on both sides and only the constraint vector is rewritten.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

omit [AddCommGroup α] [Module ℝ α] in
/-- The constraint vector, regrouped onto the constraint columns that survive.
This is `sum_monomial_merge` at `Vec ℝ m`, the exponent side knowing nothing
about which block it came from. -/
theorem ConPolyZono.aux_mulVec_compactCons (C : ConPolyZono α) (a : Fin C.p → ℝ) :
    C.compactCons.A *ᵥ PolyZonotope.monomial C.compactCons.EC a
      = C.A *ᵥ PolyZonotope.monomial C.EC a := by
  rw [ConPolyZono.mulVec_eq_sum C.compactCons.A (PolyZonotope.monomial C.compactCons.EC a),
    ConPolyZono.mulVec_eq_sum C.A (PolyZonotope.monomial C.EC a),
    PolyZonotope.sum_monomial_merge C.EC (ConPolyZono.consCol C.A) a
      (PolyZonotope.rep C.EC) (PolyZonotope.compactKeep C.EC (ConPolyZono.consCol C.A))
      (PolyZonotope.col_rep C.EC)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem C.EC (ConPolyZono.consCol C.A) hj,
    PolyZonotope.sum_compactKeep]
  rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.aux_satisfies_compactCons (C : ConPolyZono α) (a : Fin C.p → ℝ) :
    C.satisfies a ↔ C.compactCons.satisfies a :=
  ConPolyZono.holds_congr (ConPolyZono.aux_mulVec_compactCons C a)

-- the generators are copied, so the point equation is the same term on both sides
theorem ConPolyZono.compactCons_exact (C : ConPolyZono α) :
    C.construct = C.compactCons.construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, (ConPolyZono.aux_satisfies_compactCons C a).mp hsat, rfl⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, (ConPolyZono.aux_satisfies_compactCons C a).mpr hsat, rfl⟩

end CORALean.Real
