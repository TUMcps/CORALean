import CORALean.ContSet.ConPolyZono.Real.Operations.AbsFactorExtendLeOne
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendLeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendRight
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxLeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxRight
import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx
import CORALean.ContSet.ConPolyZono.Real.Operations.CompactFactors
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsCongr

/-!
# Dropping the factors neither block reads loses nothing

`compactFactors` changes `p`, so its two directions differ: one restricts a
factor vector to the kept factors, the other extends one by zero — a value the
dropped factors are free to take, since no monomial of either block reads them.
The constraint monomials restrict alongside the generator ones, and nothing else
moves.

The two `key`s are stated with the *original* centre and independent block on
both sides. They are the compacted ones up to unfolding, and writing them so
keeps each equation to the one sum that actually changes.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The generator sum read against the kept factors alone. -/
theorem ConPolyZono.aux_sum_compactFactors (C : ConPolyZono α) (a : Fin C.p → ℝ) :
    (∑ i, PolyZonotope.monomial C.E a i • C.G i)
      = ∑ i : Fin C.compactFactors.h, PolyZonotope.monomial C.compactFactors.E
          (fun k => a (ConPolyZono.factorIdx C.E C.EC k)) i • C.compactFactors.G i := by
  show (∑ i, PolyZonotope.monomial C.E a i • C.G i)
      = ∑ i : Fin C.h, PolyZonotope.monomial
          (fun k i => C.E (ConPolyZono.factorIdx C.E C.EC k) i)
          (fun k => a (ConPolyZono.factorIdx C.E C.EC k)) i • C.G i
  exact Finset.sum_congr rfl fun i _ => by rw [ConPolyZono.monomial_factorIdx_left]

/-- The same sum against an extended factor vector, which is what the reverse
inclusion supplies. Stated separately, since obtaining it from
`sum_compactFactors` would rewrite under a binder typed by a projection. -/
theorem ConPolyZono.aux_sum_compactFactors_extend (C : ConPolyZono α)
    (a : Fin C.compactFactors.p → ℝ) :
    (∑ i, PolyZonotope.monomial C.E (ConPolyZono.factorExtend C.E C.EC a) i • C.G i)
      = ∑ i : Fin C.compactFactors.h,
          PolyZonotope.monomial C.compactFactors.E a i • C.compactFactors.G i := by
  show (∑ i, PolyZonotope.monomial C.E (ConPolyZono.factorExtend C.E C.EC a) i • C.G i)
      = ∑ i : Fin C.h,
          PolyZonotope.monomial (fun k i => C.E (ConPolyZono.factorIdx C.E C.EC k) i) a i
            • C.G i
  exact Finset.sum_congr rfl fun i _ => by rw [ConPolyZono.monomial_factorExtend_left]

-- the constraint monomials restrict alongside the generator ones, and nothing else moves
omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.aux_satisfies_compactFactors (C : ConPolyZono α) (a : Fin C.p → ℝ) :
    C.satisfies a
      ↔ C.compactFactors.satisfies fun k => a (ConPolyZono.factorIdx C.E C.EC k) := by
  refine ConPolyZono.holds_congr ?_
  have hm : PolyZonotope.monomial C.compactFactors.EC
        (fun k => a (ConPolyZono.factorIdx C.E C.EC k))
      = PolyZonotope.monomial C.EC a :=
    funext fun l => ConPolyZono.monomial_factorIdx_right C.E C.EC a l
  rw [hm]
  rfl

-- and the same the other way, a dropped factor coming back as zero
omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.aux_satisfies_compactFactors_extend (C : ConPolyZono α)
    (a : Fin C.compactFactors.p → ℝ) :
    C.satisfies (ConPolyZono.factorExtend C.E C.EC a) ↔ C.compactFactors.satisfies a := by
  refine ConPolyZono.holds_congr ?_
  have hm : PolyZonotope.monomial C.compactFactors.EC a
      = PolyZonotope.monomial C.EC (ConPolyZono.factorExtend C.E C.EC a) :=
    funext fun l => (ConPolyZono.monomial_factorExtend_right C.E C.EC a l).symm
  rw [hm]
  rfl

theorem ConPolyZono.compactFactors_exact (C : ConPolyZono α) :
    C.construct = C.compactFactors.construct := by
  have key : ∀ (a : Fin C.p → ℝ) (β : Fin C.q → ℝ),
      C.c + (∑ i, PolyZonotope.monomial C.E a i • C.G i) + ∑ j, β j • C.GI j
        = C.c + (∑ i : Fin C.compactFactors.h, PolyZonotope.monomial C.compactFactors.E
            (fun k => a (ConPolyZono.factorIdx C.E C.EC k)) i • C.compactFactors.G i)
          + ∑ j, β j • C.GI j :=
    fun a _ => by rw [ConPolyZono.aux_sum_compactFactors C a]
  -- and the same the other way, the dropped factors coming back as zero
  have key' : ∀ (a : Fin C.compactFactors.p → ℝ) (β : Fin C.q → ℝ),
      C.c + (∑ i, PolyZonotope.monomial C.E (ConPolyZono.factorExtend C.E C.EC a) i • C.G i)
          + ∑ j, β j • C.GI j
        = C.c + (∑ i : Fin C.compactFactors.h,
            PolyZonotope.monomial C.compactFactors.E a i • C.compactFactors.G i)
          + ∑ j, β j • C.GI j :=
    fun a _ => by rw [ConPolyZono.aux_sum_compactFactors_extend C a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨fun k => a (ConPolyZono.factorIdx C.E C.EC k), β, fun k => ha _, hβ,
      (ConPolyZono.aux_satisfies_compactFactors C a).mp hsat, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨ConPolyZono.factorExtend C.E C.EC a, β,
      fun k => ConPolyZono.abs_factorExtend_le_one C.E C.EC ha k, hβ,
      (ConPolyZono.aux_satisfies_compactFactors_extend C a).mpr hsat, (key' a β).symm⟩

end CORALean.Real
