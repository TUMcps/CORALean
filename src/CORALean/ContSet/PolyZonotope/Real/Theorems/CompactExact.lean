import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# Compaction loses nothing

Every step is an equality of sets and needs no hypothesis, which is the point:
`compact` is bookkeeping, and an order bound is only worth stating once the
bookkeeping is done.

The two stages pay in different coin. `compactGens` touches neither `p` nor `q`,
so one factor vector reads both sides and both inclusions come out of the single
equation `sum_compactGens`. `compactFactors` changes `p`, so the directions
differ: one restricts a factor vector to the kept factors, the other extends one
by zero — a value the dropped factors are free to take, since no monomial reads
them.

Each `key` below is stated with the *original* centre and independent block on
both sides. They are the compacted ones up to unfolding, and writing them so
keeps the equation to the one sum that actually changes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem PolyZonotope.sum_compactGens (PZ : PolyZonotope α) (a : Fin PZ.p → ℝ) :
    (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i)
      = ∑ j : Fin PZ.compactGens.h,
          PolyZonotope.monomial PZ.compactGens.E a j • PZ.compactGens.G j := by
  rw [PolyZonotope.sum_monomial_merge PZ.E PZ.G a (PolyZonotope.rep PZ.E)
      (PolyZonotope.compactKeep PZ.E PZ.G) (PolyZonotope.col_rep PZ.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem PZ.E PZ.G hj,
    PolyZonotope.sum_compactKeep]
  rfl

theorem PolyZonotope.compactGens_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.compactGens.construct := by
  have key : ∀ (a : Fin PZ.p → ℝ) (β : Fin PZ.q → ℝ),
      PZ.c + (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i) + ∑ j, β j • PZ.GI j
        = PZ.c + (∑ j : Fin PZ.compactGens.h,
            PolyZonotope.monomial PZ.compactGens.E a j • PZ.compactGens.G j)
          + ∑ j, β j • PZ.GI j :=
    fun a _ => by rw [PolyZonotope.sum_compactGens PZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, (key a β).symm⟩

/-- The same sum read against the kept factors alone. -/
theorem PolyZonotope.sum_compactFactors (PZ : PolyZonotope α) (a : Fin PZ.p → ℝ) :
    (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i)
      = ∑ i : Fin PZ.compactFactors.h, PolyZonotope.monomial PZ.compactFactors.E
          (fun k => a (PolyZonotope.factorIdx PZ.E k)) i • PZ.compactFactors.G i := by
  show (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i)
      = ∑ i : Fin PZ.h,
          PolyZonotope.monomial (fun k i => PZ.E (PolyZonotope.factorIdx PZ.E k) i)
            (fun k => a (PolyZonotope.factorIdx PZ.E k)) i • PZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_factorIdx]

/-- The same sum against an extended factor vector, which is what the reverse
inclusion supplies. Stated separately rather than obtained from
`sum_compactFactors` by substitution: the substituted vector would have to be
rewritten under a binder whose type is a projection, which `rw` will not do. -/
theorem PolyZonotope.sum_compactFactors_extend (PZ : PolyZonotope α)
    (a : Fin PZ.compactFactors.p → ℝ) :
    (∑ i, PolyZonotope.monomial PZ.E (PolyZonotope.factorExtend PZ.E a) i • PZ.G i)
      = ∑ i : Fin PZ.compactFactors.h,
          PolyZonotope.monomial PZ.compactFactors.E a i • PZ.compactFactors.G i := by
  show (∑ i, PolyZonotope.monomial PZ.E (PolyZonotope.factorExtend PZ.E a) i • PZ.G i)
      = ∑ i : Fin PZ.h,
          PolyZonotope.monomial (fun k i => PZ.E (PolyZonotope.factorIdx PZ.E k) i) a i
            • PZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_factorExtend]

theorem PolyZonotope.compactFactors_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.compactFactors.construct := by
  have key : ∀ (a : Fin PZ.p → ℝ) (β : Fin PZ.q → ℝ),
      PZ.c + (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i) + ∑ j, β j • PZ.GI j
        = PZ.c + (∑ i : Fin PZ.compactFactors.h, PolyZonotope.monomial PZ.compactFactors.E
            (fun k => a (PolyZonotope.factorIdx PZ.E k)) i • PZ.compactFactors.G i)
          + ∑ j, β j • PZ.GI j :=
    fun a _ => by rw [PolyZonotope.sum_compactFactors PZ a]
  have key' : ∀ (a : Fin PZ.compactFactors.p → ℝ) (β : Fin PZ.q → ℝ),
      PZ.c + (∑ i, PolyZonotope.monomial PZ.E (PolyZonotope.factorExtend PZ.E a) i • PZ.G i)
          + ∑ j, β j • PZ.GI j
        = PZ.c + (∑ i : Fin PZ.compactFactors.h,
            PolyZonotope.monomial PZ.compactFactors.E a i • PZ.compactFactors.G i)
          + ∑ j, β j • PZ.GI j :=
    fun a _ => by rw [PolyZonotope.sum_compactFactors_extend PZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨fun k => a (PolyZonotope.factorIdx PZ.E k), β, fun k => ha _, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨PolyZonotope.factorExtend PZ.E a, β,
      fun k => PolyZonotope.abs_factorExtend_le_one PZ.E ha k, hβ, (key' a β).symm⟩

/-- CORA's `compact`, and what an order bound rests on: the set is unchanged. -/
theorem PolyZonotope.compact_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.compact.construct :=
  (PolyZonotope.compactGens_exact PZ).trans
    (PolyZonotope.compactFactors_exact PZ.compactGens)

end CORALean.Real
