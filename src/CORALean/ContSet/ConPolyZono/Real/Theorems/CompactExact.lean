import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Theorems.Holds

/-!
# Compaction loses nothing

Three stages and three equalities of sets, none of them needing a hypothesis:
`compact` is bookkeeping, and an order bound is only worth stating once the
bookkeeping is done.

Each stage pays in its own coin. `compactGens` leaves the whole constraint block
alone, so `satisfies` transfers by definition and only the generator sum moves.
`compactCons` leaves the generators alone and moves only `A μ(α)`, which
`holds_congr` is exactly the statement about. `compactFactors` changes `p`, so
its two directions differ: one restricts a factor vector to the kept factors,
the other extends one by zero — a value the dropped factors are free to take,
since no monomial of either block reads them.

Each `key` below is stated with the *original* centre and independent block on
both sides. They are the compacted ones up to unfolding, and writing them so
keeps the equation to the one sum that actually changes.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-! ## The generators -/

/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem ConPolyZono.sum_compactGens (C : ConPolyZono α) (a : Fin C.p → ℝ) :
    (∑ i, PolyZonotope.monomial C.E a i • C.G i)
      = ∑ j : Fin C.compactGens.h,
          PolyZonotope.monomial C.compactGens.E a j • C.compactGens.G j := by
  rw [PolyZonotope.sum_monomial_merge C.E C.G a (PolyZonotope.rep C.E)
      (PolyZonotope.compactKeep C.E C.G) (PolyZonotope.col_rep C.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem C.E C.G hj,
    PolyZonotope.sum_compactKeep]
  rfl

-- the constraint block is copied, so one factor vector answers for both sides
theorem ConPolyZono.compactGens_exact (C : ConPolyZono α) :
    C.construct = C.compactGens.construct := by
  have key : ∀ (a : Fin C.p → ℝ) (β : Fin C.q → ℝ),
      C.c + (∑ i, PolyZonotope.monomial C.E a i • C.G i) + ∑ j, β j • C.GI j
        = C.c + (∑ j : Fin C.compactGens.h,
            PolyZonotope.monomial C.compactGens.E a j • C.compactGens.G j)
          + ∑ j, β j • C.GI j :=
    fun a _ => by rw [ConPolyZono.sum_compactGens C a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, (key a β).symm⟩

/-! ## The constraints -/

omit [AddCommGroup α] [Module ℝ α] in
/-- The constraint vector, regrouped onto the constraint columns that survive.
This is `sum_monomial_merge` at `Vec ℝ m`, the exponent side knowing nothing
about which block it came from. -/
theorem ConPolyZono.mulVec_compactCons (C : ConPolyZono α) (a : Fin C.p → ℝ) :
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
theorem ConPolyZono.satisfies_compactCons (C : ConPolyZono α) (a : Fin C.p → ℝ) :
    C.satisfies a ↔ C.compactCons.satisfies a :=
  ConPolyZono.holds_congr (ConPolyZono.mulVec_compactCons C a)

-- the generators are copied, so the point equation is the same term on both sides
theorem ConPolyZono.compactCons_exact (C : ConPolyZono α) :
    C.construct = C.compactCons.construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, (ConPolyZono.satisfies_compactCons C a).mp hsat, rfl⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, (ConPolyZono.satisfies_compactCons C a).mpr hsat, rfl⟩

/-! ## The factors -/

/-- The generator sum read against the kept factors alone. -/
theorem ConPolyZono.sum_compactFactors (C : ConPolyZono α) (a : Fin C.p → ℝ) :
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
theorem ConPolyZono.sum_compactFactors_extend (C : ConPolyZono α)
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
theorem ConPolyZono.satisfies_compactFactors (C : ConPolyZono α) (a : Fin C.p → ℝ) :
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
theorem ConPolyZono.satisfies_compactFactors_extend (C : ConPolyZono α)
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
    fun a _ => by rw [ConPolyZono.sum_compactFactors C a]
  -- and the same the other way, the dropped factors coming back as zero
  have key' : ∀ (a : Fin C.compactFactors.p → ℝ) (β : Fin C.q → ℝ),
      C.c + (∑ i, PolyZonotope.monomial C.E (ConPolyZono.factorExtend C.E C.EC a) i • C.G i)
          + ∑ j, β j • C.GI j
        = C.c + (∑ i : Fin C.compactFactors.h,
            PolyZonotope.monomial C.compactFactors.E a i • C.compactFactors.G i)
          + ∑ j, β j • C.GI j :=
    fun a _ => by rw [ConPolyZono.sum_compactFactors_extend C a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨fun k => a (ConPolyZono.factorIdx C.E C.EC k), β, fun k => ha _, hβ,
      (ConPolyZono.satisfies_compactFactors C a).mp hsat, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨ConPolyZono.factorExtend C.E C.EC a, β,
      fun k => ConPolyZono.abs_factorExtend_le_one C.E C.EC ha k, hβ,
      (ConPolyZono.satisfies_compactFactors_extend C a).mpr hsat, (key' a β).symm⟩

/-- CORA's `compact`, and what an order bound would rest on: the set is
unchanged by any of the three stages. -/
theorem ConPolyZono.compact_exact (C : ConPolyZono α) :
    C.construct = C.compact.construct :=
  (ConPolyZono.compactGens_exact C).trans
    ((ConPolyZono.compactCons_exact C.compactGens).trans
      (ConPolyZono.compactFactors_exact C.compactGens.compactCons))

end CORALean.Real
