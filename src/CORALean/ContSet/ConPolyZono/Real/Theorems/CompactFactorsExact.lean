module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AbsFactorExtendLeOne
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendLeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorExtendRight
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxLeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxRight
public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx
public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsCongr

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generator sum read against the kept factors alone. -/
theorem ConPolyZono.aux_sum_compactFactors (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) :
    (∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i)
      = ∑ i : Fin cPZ.compactFactors.h, PolyZonotope.monomial cPZ.compactFactors.E
          (fun k => a (ConPolyZono.factorIdx cPZ.E cPZ.EC k)) i
            • cPZ.compactFactors.G i := by -- --- PROOF ---
  show (∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i)
      = ∑ i : Fin cPZ.h, PolyZonotope.monomial
          (fun k i => cPZ.E (ConPolyZono.factorIdx cPZ.E cPZ.EC k) i)
          (fun k => a (ConPolyZono.factorIdx cPZ.E cPZ.EC k)) i • cPZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [ConPolyZono.monomial_factorIdx_left]

/-- The same sum against an extended factor vector, which is what the reverse
inclusion supplies. Stated separately, since obtaining it from
`sum_compactFactors` would rewrite under a binder typed by a projection. -/
theorem ConPolyZono.aux_sum_compactFactors_extend (cPZ : ConPolyZono α)
    (a : Fin cPZ.compactFactors.p → ℝ) :
    (∑ i, PolyZonotope.monomial cPZ.E (ConPolyZono.factorExtend cPZ.E cPZ.EC a) i • cPZ.G i)
      = ∑ i : Fin cPZ.compactFactors.h,
          PolyZonotope.monomial cPZ.compactFactors.E a i
            • cPZ.compactFactors.G i := by -- --- PROOF ---
  show (∑ i, PolyZonotope.monomial cPZ.E (ConPolyZono.factorExtend cPZ.E cPZ.EC a) i • cPZ.G i)
      = ∑ i : Fin cPZ.h,
          PolyZonotope.monomial (fun k i => cPZ.E (ConPolyZono.factorIdx cPZ.E cPZ.EC k) i) a i
            • cPZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [ConPolyZono.monomial_factorExtend_left]

-- the constraint monomials restrict alongside the generator ones, and nothing else moves
omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.aux_satisfies_compactFactors (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) :
    cPZ.satisfies a
      ↔ cPZ.compactFactors.satisfies fun k =>
        a (ConPolyZono.factorIdx cPZ.E cPZ.EC k) := by -- --- PROOF ---
  refine ConPolyZono.holds_congr ?_
  have hm : PolyZonotope.monomial cPZ.compactFactors.EC
        (fun k => a (ConPolyZono.factorIdx cPZ.E cPZ.EC k))
      = PolyZonotope.monomial cPZ.EC a :=
    funext fun l => ConPolyZono.monomial_factorIdx_right cPZ.E cPZ.EC a l
  rw [hm]
  rfl

-- and the same the other way, a dropped factor coming back as zero
omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.aux_satisfies_compactFactors_extend (cPZ : ConPolyZono α)
    (a : Fin cPZ.compactFactors.p → ℝ) :
    cPZ.satisfies (ConPolyZono.factorExtend cPZ.E cPZ.EC a)
      ↔ cPZ.compactFactors.satisfies a := by -- --- PROOF ---
  refine ConPolyZono.holds_congr ?_
  have hm : PolyZonotope.monomial cPZ.compactFactors.EC a
      = PolyZonotope.monomial cPZ.EC (ConPolyZono.factorExtend cPZ.E cPZ.EC a) :=
    funext fun l => (ConPolyZono.monomial_factorExtend_right cPZ.E cPZ.EC a l).symm
  rw [hm]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactFactors_exact (cPZ : ConPolyZono α) :
    cPZ.construct = cPZ.compactFactors.construct := by -- --- PROOF ---
  have key : ∀ (a : Fin cPZ.p → ℝ) (β : Fin cPZ.q → ℝ),
      cPZ.c + (∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i) + ∑ j, β j • cPZ.GI j
        = cPZ.c + (∑ i : Fin cPZ.compactFactors.h, PolyZonotope.monomial cPZ.compactFactors.E
            (fun k => a (ConPolyZono.factorIdx cPZ.E cPZ.EC k)) i • cPZ.compactFactors.G i)
          + ∑ j, β j • cPZ.GI j :=
    fun a _ => by rw [ConPolyZono.aux_sum_compactFactors cPZ a]
  -- and the same the other way, the dropped factors coming back as zero
  have key' : ∀ (a : Fin cPZ.compactFactors.p → ℝ) (β : Fin cPZ.q → ℝ),
      cPZ.c + (∑ i, PolyZonotope.monomial cPZ.E
          (ConPolyZono.factorExtend cPZ.E cPZ.EC a) i • cPZ.G i)
          + ∑ j, β j • cPZ.GI j
        = cPZ.c + (∑ i : Fin cPZ.compactFactors.h,
            PolyZonotope.monomial cPZ.compactFactors.E a i • cPZ.compactFactors.G i)
          + ∑ j, β j • cPZ.GI j :=
    fun a _ => by rw [ConPolyZono.aux_sum_compactFactors_extend cPZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨fun k => a (ConPolyZono.factorIdx cPZ.E cPZ.EC k), β, fun k => ha _, hβ,
      (ConPolyZono.aux_satisfies_compactFactors cPZ a).mp hsat, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨ConPolyZono.factorExtend cPZ.E cPZ.EC a, β,
      fun k => ConPolyZono.abs_factorExtend_le_one cPZ.E cPZ.EC ha k, hβ,
      (ConPolyZono.aux_satisfies_compactFactors_extend cPZ a).mpr hsat, (key' a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
