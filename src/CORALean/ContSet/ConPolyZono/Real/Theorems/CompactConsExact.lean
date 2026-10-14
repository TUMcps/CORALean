module

public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecEqSum
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsCongr
public import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMem
public import CORALean.ContSet.PolyZonotope.Real.Operations.SumCompactKeep
public import CORALean.ContSet.PolyZonotope.Real.Operations.SumMonomialMerge

@[expose] public section

/-!
# Merging equal constraint exponent columns loses nothing

The result is [1, Prop. 2], the constraint-side counterpart.

`compactCons` leaves the generators alone and moves only `A μ(α)`, which
`holds_congr` is exactly the statement about, so the point equation is the same
term on both sides and only the constraint vector is rewritten.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [AddCommGroup α] [Module ℝ α] in
/-- The constraint vector, regrouped onto the constraint columns that survive.
This is `sum_monomial_merge` at `Vec ℝ m`, the exponent side knowing nothing
about which block it came from. -/
theorem ConPolyZono.aux_mulVec_compactCons (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) :
    cPZ.compactCons.A *ᵥ PolyZonotope.monomial cPZ.compactCons.EC a
      = cPZ.A *ᵥ PolyZonotope.monomial cPZ.EC a := by -- --- PROOF ---
  rw [ConPolyZono.mulVec_eq_sum cPZ.compactCons.A (PolyZonotope.monomial cPZ.compactCons.EC a),
    ConPolyZono.mulVec_eq_sum cPZ.A (PolyZonotope.monomial cPZ.EC a),
    PolyZonotope.sum_monomial_merge cPZ.EC (ConPolyZono.consCol cPZ.A) a
      (PolyZonotope.rep cPZ.EC) (PolyZonotope.compactKeep cPZ.EC (ConPolyZono.consCol cPZ.A))
      (PolyZonotope.col_rep cPZ.EC)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem cPZ.EC (ConPolyZono.consCol cPZ.A) hj,
    PolyZonotope.sum_compactKeep]
  rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.aux_satisfies_compactCons (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) :
    cPZ.satisfies a ↔ cPZ.compactCons.satisfies a :=
  ConPolyZono.holds_congr (ConPolyZono.aux_mulVec_compactCons cPZ a)


-- =======================================  MAIN THEOREM  ======================================= --

-- the generators are copied, so the point equation is the same term on both sides
theorem ConPolyZono.compactCons_exact (cPZ : ConPolyZono α) :
    cPZ.construct = cPZ.compactCons.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, (ConPolyZono.aux_satisfies_compactCons cPZ a).mp hsat, rfl⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, (ConPolyZono.aux_satisfies_compactCons cPZ a).mpr hsat, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
