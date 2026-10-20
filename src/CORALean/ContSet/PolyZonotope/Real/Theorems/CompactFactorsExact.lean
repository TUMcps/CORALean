module

public import CORALean.ContSet.PolyZonotope.Real.Operations.AbsFactorExtendLeOne
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Real.Operations.CompactFactors
public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtend
public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx
public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorIdx
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorExtend
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorIdx
public import CORALean.ContSet.PolyZonotope.Real.Operations.UsedFactors

@[expose] public section

/-!
# Dropping the factors no monomial reads loses nothing

`compactFactors` changes `p`, so the two directions differ: one restricts a
factor vector to the kept factors, the other extends one by zero — a value the
dropped factors are free to take, since no monomial reads them.

The two `key`s are stated with the *original* center and independent block on
both sides. They are the compacted ones up to unfolding, and writing them so
keeps each equation to the one sum that actually changes.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* dropping unused factors leaves the set unchanged
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same sum read against the kept factors alone. -/
theorem PolyZonotope.aux_sum_compactFactors (pZ : PolyZonotope α)
    (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ i : Fin pZ.compactFactors.h, PolyZonotope.monomial pZ.compactFactors.E
          (fun k => a (PolyZonotope.factorIdx pZ.E k)) i
            • pZ.compactFactors.G i := by -- --- PROOF ---
  show (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ i : Fin pZ.h,
          PolyZonotope.monomial (fun k i => pZ.E (PolyZonotope.factorIdx pZ.E k) i)
            (fun k => a (PolyZonotope.factorIdx pZ.E k)) i • pZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_factorIdx]

/-- The same sum against an extended factor vector, which is what the reverse
inclusion supplies. Stated separately, since obtaining it from
`sum_compactFactors` would rewrite under a binder typed by a projection. -/
theorem PolyZonotope.aux_sum_compactFactors_extend (pZ : PolyZonotope α)
    (a : Fin pZ.compactFactors.p → ℝ) : -- --- CONCL ---
    (∑ i, PolyZonotope.monomial pZ.E (PolyZonotope.factorExtend pZ.E a) i • pZ.G i)
      = ∑ i : Fin pZ.compactFactors.h,
          PolyZonotope.monomial pZ.compactFactors.E a i
            • pZ.compactFactors.G i := by -- --- PROOF ---
  show (∑ i, PolyZonotope.monomial pZ.E (PolyZonotope.factorExtend pZ.E a) i • pZ.G i)
      = ∑ i : Fin pZ.h,
          PolyZonotope.monomial (fun k i => pZ.E (PolyZonotope.factorIdx pZ.E k) i) a i
            • pZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_factorExtend]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compactFactors_exact (pZ : PolyZonotope α) : -- --- CONCL ---
    pZ.construct = pZ.compactFactors.construct := by -- --- PROOF ---
  have key : ∀ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ),
      pZ.c + (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i) + ∑ j, β j • pZ.GI j
        = pZ.c + (∑ i : Fin pZ.compactFactors.h, PolyZonotope.monomial pZ.compactFactors.E
            (fun k => a (PolyZonotope.factorIdx pZ.E k)) i • pZ.compactFactors.G i)
          + ∑ j, β j • pZ.GI j :=
    fun a _ => by rw [PolyZonotope.aux_sum_compactFactors pZ a]
  -- and the same the other way, a dropped factor coming back as zero
  have key' : ∀ (a : Fin pZ.compactFactors.p → ℝ) (β : Fin pZ.q → ℝ),
      pZ.c + (∑ i, PolyZonotope.monomial pZ.E (PolyZonotope.factorExtend pZ.E a) i • pZ.G i)
          + ∑ j, β j • pZ.GI j
        = pZ.c + (∑ i : Fin pZ.compactFactors.h,
            PolyZonotope.monomial pZ.compactFactors.E a i • pZ.compactFactors.G i)
          + ∑ j, β j • pZ.GI j :=
    fun a _ => by rw [PolyZonotope.aux_sum_compactFactors_extend pZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨fun k => a (PolyZonotope.factorIdx pZ.E k), β, fun k => ha _, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨PolyZonotope.factorExtend pZ.E a, β,
      fun k => PolyZonotope.abs_factorExtend_le_one pZ.E ha k, hβ, (key' a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
