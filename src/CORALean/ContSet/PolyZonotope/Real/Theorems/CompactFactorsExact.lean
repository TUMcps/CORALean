import CORALean.ContSet.PolyZonotope.Real.Operations.AbsFactorExtendLeOne
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactFactors
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtend
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorExtend
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.UsedFactors

/-!
# Dropping the factors no monomial reads loses nothing

`compactFactors` changes `p`, so the two directions differ: one restricts a
factor vector to the kept factors, the other extends one by zero — a value the
dropped factors are free to take, since no monomial reads them.

The two `key`s are stated with the *original* centre and independent block on
both sides. They are the compacted ones up to unfolding, and writing them so
keeps each equation to the one sum that actually changes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same sum read against the kept factors alone. -/
theorem PolyZonotope.aux_sum_compactFactors (PZ : PolyZonotope α) (a : Fin PZ.p → ℝ) :
    (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i)
      = ∑ i : Fin PZ.compactFactors.h, PolyZonotope.monomial PZ.compactFactors.E
          (fun k => a (PolyZonotope.factorIdx PZ.E k)) i • PZ.compactFactors.G i := by
  show (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i)
      = ∑ i : Fin PZ.h,
          PolyZonotope.monomial (fun k i => PZ.E (PolyZonotope.factorIdx PZ.E k) i)
            (fun k => a (PolyZonotope.factorIdx PZ.E k)) i • PZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_factorIdx]

/-- The same sum against an extended factor vector, which is what the reverse
inclusion supplies. Stated separately, since obtaining it from
`sum_compactFactors` would rewrite under a binder typed by a projection. -/
theorem PolyZonotope.aux_sum_compactFactors_extend (PZ : PolyZonotope α)
    (a : Fin PZ.compactFactors.p → ℝ) :
    (∑ i, PolyZonotope.monomial PZ.E (PolyZonotope.factorExtend PZ.E a) i • PZ.G i)
      = ∑ i : Fin PZ.compactFactors.h,
          PolyZonotope.monomial PZ.compactFactors.E a i • PZ.compactFactors.G i := by
  show (∑ i, PolyZonotope.monomial PZ.E (PolyZonotope.factorExtend PZ.E a) i • PZ.G i)
      = ∑ i : Fin PZ.h,
          PolyZonotope.monomial (fun k i => PZ.E (PolyZonotope.factorIdx PZ.E k) i) a i
            • PZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_factorExtend]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compactFactors_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.compactFactors.construct := by
  have key : ∀ (a : Fin PZ.p → ℝ) (β : Fin PZ.q → ℝ),
      PZ.c + (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i) + ∑ j, β j • PZ.GI j
        = PZ.c + (∑ i : Fin PZ.compactFactors.h, PolyZonotope.monomial PZ.compactFactors.E
            (fun k => a (PolyZonotope.factorIdx PZ.E k)) i • PZ.compactFactors.G i)
          + ∑ j, β j • PZ.GI j :=
    fun a _ => by rw [PolyZonotope.aux_sum_compactFactors PZ a]
  -- and the same the other way, a dropped factor coming back as zero
  have key' : ∀ (a : Fin PZ.compactFactors.p → ℝ) (β : Fin PZ.q → ℝ),
      PZ.c + (∑ i, PolyZonotope.monomial PZ.E (PolyZonotope.factorExtend PZ.E a) i • PZ.G i)
          + ∑ j, β j • PZ.GI j
        = PZ.c + (∑ i : Fin PZ.compactFactors.h,
            PolyZonotope.monomial PZ.compactFactors.E a i • PZ.compactFactors.G i)
          + ∑ j, β j • PZ.GI j :=
    fun a _ => by rw [PolyZonotope.aux_sum_compactFactors_extend PZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨fun k => a (PolyZonotope.factorIdx PZ.E k), β, fun k => ha _, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨PolyZonotope.factorExtend PZ.E a, β,
      fun k => PolyZonotope.abs_factorExtend_le_one PZ.E ha k, hβ, (key' a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
