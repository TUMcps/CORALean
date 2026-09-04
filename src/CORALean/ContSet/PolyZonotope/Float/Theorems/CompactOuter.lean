import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact

/-!
# Compaction encloses, where the exact one is an equality

The single place the two layers' `compact` differ, and it is the merge: adding
the entries of a class rounds, so the exact fibre sum is bracketed by the two
directed masked sums, the lower is stored, and the gap is a `generatorError` —
the merged column's coefficient being a monomial in `[-1,1]`.

Everything else transfers untouched. `sum_monomial_merge` is the exact layer's
and knows nothing about a scalar; `repKeep` replaces `compactKeep` only because
the zero test is gone, and the fibre of a non-representative is empty either
way, which `rep_idem` is what says.

`compactFactors` costs nothing at all: it changes `p` and the exponent matrix,
both over ℕ, so the nominal part of the result *is* the exact layer's
`compactFactors` of the nominal part, and `compactFactors_exact` applies to it
verbatim.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p h : ℕ}

-- each `min'_le` re-elaborates the decidability instance of the filter it ranges over
set_option maxHeartbeats 400000 in
/-- The least index of a class is the least index of its own class, which makes
a non-representative's fibre empty. The two finsets are named rather than left
to unification, `rep` unfolding to a `min'` over a filter. -/
theorem PolyZonotope.rep_idem (E : Fin p → Fin h → ℕ) (i : Fin h) :
    Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i) = Real.PolyZonotope.rep E i := by
  have hcol : Real.PolyZonotope.col E (Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i))
      = Real.PolyZonotope.col E i := by
    rw [Real.PolyZonotope.col_rep, Real.PolyZonotope.col_rep]
  have h₁ : Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i)
      ≤ Real.PolyZonotope.rep E i :=
    Finset.min'_le
      (Finset.univ.filter fun i' => Real.PolyZonotope.col E i'
        = Real.PolyZonotope.col E (Real.PolyZonotope.rep E i))
      (Real.PolyZonotope.rep E i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  have h₂ : Real.PolyZonotope.rep E i
      ≤ Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i) :=
    Finset.min'_le
      (Finset.univ.filter fun i' => Real.PolyZonotope.col E i' = Real.PolyZonotope.col E i)
      (Real.PolyZonotope.rep E (Real.PolyZonotope.rep E i))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcol⟩)
  exact le_antisymm h₁ h₂

/-- A column that is not its class's representative gathers nothing. -/
theorem PolyZonotope.fiber_eq_zero_of_notMem (E : Fin p → Fin h → ℕ) (Gr : Fin h → ℝ)
    {j : Fin h} (hj : j ∉ PolyZonotope.repKeep E) :
    Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E) Gr j = 0 := by
  rw [Real.PolyZonotope.fiberSum]
  refine Finset.sum_eq_zero fun l hl => ?_
  exfalso
  have hrl : Real.PolyZonotope.rep E l = j := (Finset.mem_filter.mp hl).2
  refine hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
  rw [← hrl, PolyZonotope.rep_idem]

/-- A sum over the kept columns, read against a plain count. -/
theorem PolyZonotope.aux_sum_keep (s : Finset (Fin h)) (f : Fin h → ℝ) :
    ∑ j ∈ s, f j = ∑ j : Fin s.card, f (s.orderIsoOfFin rfl j) := by
  rw [← Finset.sum_coe_sort s f]
  exact (Equiv.sum_comp (s.orderIsoOfFin rfl).toEquiv fun x => f x).symm

/-- The masked sum is the fibre sum: outside the fibre every summand is `zero`,
which reads as `0`. -/
theorem PolyZonotope.aux_sum_mask (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n)
    (j : Fin h) :
    (∑ l, toReal (if r l = j then G i l else zero))
      = Real.PolyZonotope.fiberSum r (fun l => toReal (G i l)) j := by
  rw [Real.PolyZonotope.fiberSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : r l = j
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl, toReal_zero]

-- so the two directed masked sums bracket the exact fibre from either side
theorem PolyZonotope.fiberDown_le (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n)
    (j : Fin h) :
    toReal (PolyZonotope.fiberDown r G i j)
      ≤ Real.PolyZonotope.fiberSum r (fun l => toReal (G i l)) j := by
  rw [← PolyZonotope.aux_sum_mask r G i j]
  exact sumDown_le_sum _

theorem PolyZonotope.le_fiberUp (r : Fin h → Fin h) (G : Mat 𝕋 n h) (i : Fin n)
    (j : Fin h) :
    Real.PolyZonotope.fiberSum r (fun l => toReal (G i l)) j
      ≤ toReal (PolyZonotope.fiberUp r G i j) := by
  rw [← PolyZonotope.aux_sum_mask r G i j]
  exact sum_le_sumUp _

/-- The exact layer's regrouping at this layer's stored generators, the merged
columns still exact reals. -/
theorem PolyZonotope.aux_merge (PZ : PolyZonotope 𝕋 n) (a : Fin PZ.p → ℝ) (i : Fin n) :
    (∑ l, toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l)
      = ∑ j : Fin (PolyZonotope.repKeep PZ.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
              (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j)
            * Real.PolyZonotope.monomial PZ.compactGens.E a j := by
  -- the merge is the exact layer's, the stored columns being exact reals here
  calc (∑ l, toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l)
      = ∑ l, Real.PolyZonotope.monomial PZ.E a l • toReal (PZ.G i l) :=
        Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul]; exact mul_comm _ _
    _ = ∑ j ∈ PolyZonotope.repKeep PZ.E, Real.PolyZonotope.monomial PZ.E a j
          • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
              (fun l => toReal (PZ.G i l)) j :=
        Real.PolyZonotope.sum_monomial_merge PZ.E (fun l => toReal (PZ.G i l)) a
          (Real.PolyZonotope.rep PZ.E) (PolyZonotope.repKeep PZ.E)
          (Real.PolyZonotope.col_rep PZ.E)
          fun j hj => PolyZonotope.fiber_eq_zero_of_notMem PZ.E _ hj
    _ = ∑ j : Fin (PolyZonotope.repKeep PZ.E).card,
          Real.PolyZonotope.monomial PZ.E a (PolyZonotope.keepIdx PZ.E j)
            • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
                (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j) :=
        PolyZonotope.aux_sum_keep _ _
    _ = ∑ j : Fin (PolyZonotope.repKeep PZ.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
              (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j)
            * Real.PolyZonotope.monomial PZ.compactGens.E a j :=
        Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]; exact mul_comm _ _

/-- A merged column is off by at most the gap between the two directed masked
sums. -/
theorem PolyZonotope.aux_compactGap (PZ : PolyZonotope 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep PZ.E).card) :
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
        (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j)
      - toReal (PZ.mergedCol i j)| ≤ toReal (PolyZonotope.compactGap PZ i j) := by
  have hlo : toReal (PZ.mergedCol i j)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
          (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep PZ.E) PZ.G i (PolyZonotope.keepIdx PZ.E j)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
        (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j)
      ≤ toReal (PZ.mergedColUp i j) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep PZ.E) PZ.G i (PolyZonotope.keepIdx PZ.E j)
  have hgap := sub_le_subUp (PZ.mergedColUp i j) (PZ.mergedCol i j)
  rw [abs_le]
  simp only [PolyZonotope.compactGap]
  constructor <;> linarith

-- the merged column is stored downward, and that gap is what the box pays for
theorem PolyZonotope.aux_compactGens_nominal (PZ : PolyZonotope 𝕋 n) :
    nominalSet PZ ⊆ nominalSet PZ.compactGens
      + (PolyZonotope.generatorError (PolyZonotope.compactGap PZ)).construct := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  refine ⟨fun i => toReal (PZ.c i)
            + (∑ j : Fin (PolyZonotope.repKeep PZ.E).card, toReal (PZ.mergedCol i j)
                * Real.PolyZonotope.monomial PZ.compactGens.E a j)
            + ∑ j, toReal (PZ.GI i j) * β j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
          _, PolyZonotope.mem_generatorError_monomial (E := PZ.compactGens.E)
            (PZ.aux_compactGap) ha, ?_⟩
  funext i
  -- the stored merged columns and their errors recombine into the exact fibres
  have hsum : (∑ j : Fin (PolyZonotope.repKeep PZ.E).card, toReal (PZ.mergedCol i j)
        * Real.PolyZonotope.monomial PZ.compactGens.E a j)
      + (∑ j : Fin (PolyZonotope.repKeep PZ.E).card,
          (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
              (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j)
            - toReal (PZ.mergedCol i j))
            * Real.PolyZonotope.monomial PZ.compactGens.E a j)
      = ∑ j : Fin (PolyZonotope.repKeep PZ.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
              (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j)
            * Real.PolyZonotope.monomial PZ.compactGens.E a j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so `hsum` and `aux_merge` line up with it
  show toReal (PZ.c i)
        + (∑ j : Fin (PolyZonotope.repKeep PZ.E).card, toReal (PZ.mergedCol i j)
            * Real.PolyZonotope.monomial PZ.compactGens.E a j)
        + (∑ j, toReal (PZ.GI i j) * β j)
      + ∑ j : Fin (PolyZonotope.repKeep PZ.E).card,
          (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep PZ.E)
              (fun l => toReal (PZ.G i l)) (PolyZonotope.keepIdx PZ.E j)
            - toReal (PZ.mergedCol i j))
            * Real.PolyZonotope.monomial PZ.compactGens.E a j
    = x i
  rw [hxi i, PolyZonotope.aux_merge PZ a i]
  linarith [hsum]

theorem PolyZonotope.compactGens_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.compactGens.construct := by
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', d, hd, hsum⟩ := PolyZonotope.aux_compactGens_nominal PZ hz
  refine ⟨z', hz', e + d, Interval.plus_outer _ _ ⟨e, he, d, hd, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + d = z := hsum
  show z' + (e + d) = z + e
  rw [← hsum', add_comm e d, ← add_assoc]

/-- Dropping unused factors is the exact layer's step verbatim: the nominal part
of the result is `compactFactors` of the nominal part. -/
theorem PolyZonotope.compactFactors_nominal (PZ : PolyZonotope 𝕋 n) :
    nominalSet PZ = nominalSet PZ.compactFactors :=
  Real.PolyZonotope.compactFactors_exact (InflatedContSet.nominal PZ)

theorem PolyZonotope.compactFactors_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.compactFactors.construct :=
  InflatedContSet.mono_subset (PolyZonotope.compactFactors_nominal PZ).subset
    (subset_refl _)

theorem PolyZonotope.compact_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.compact.construct :=
  subset_trans (PolyZonotope.compactGens_outer PZ)
    (PolyZonotope.compactFactors_outer PZ.compactGens)

end CORALean.Float
