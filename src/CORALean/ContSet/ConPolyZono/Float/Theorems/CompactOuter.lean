import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactExact
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError

/-!
# Compaction encloses, where the exact one is an equality

Both merges add the entries of a class, so both round, and `aux_merge` is the
one statement they share: it is stated over an exponent matrix and a matrix of
stored floats and knows nothing about which block they came from, so `A`'s rows
use it as `G`'s do.

Where they differ is where the rounding goes. A merged generator column is
bracketed by the two directed masked sums, the lower is stored and the gap is a
`generatorError` in the ambient box. A merged constraint row has no ambient box
to reach — it lives in `Fin m` — so `b` absorbs it: `abs_sum_le_radius` turns
the row of gaps into one bound, the constraint monomials being in `[-1,1]`, and
`compactConsB` is `b` moved out by it on both sides. The nominal set therefore
only *grows* at that stage, and the error box does not move.

`compactFactors` costs nothing at all: it changes `p` and both exponent
matrices, all over ℕ, so the nominal part of the result *is* the exact layer's
`compactFactors` of the nominal part.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-! ## What both merges share -/

/-- A sum over the kept columns, read against a plain count. -/
theorem ConPolyZono.aux_sum_keep {d : ℕ} (t : Finset (Fin d)) (f : Fin d → ℝ) :
    ∑ j ∈ t, f j = ∑ j : Fin t.card, f (t.orderIsoOfFin rfl j) := by
  rw [← Finset.sum_coe_sort t f]
  exact (Equiv.sum_comp (t.orderIsoOfFin rfl).toEquiv fun x => f x).symm

/-- The exact layer's regrouping at this layer's stored columns, which are exact
reals. `E'` is passed rather than computed, so the caller's own field is what
appears in the result. -/
theorem ConPolyZono.aux_merge {p d h : ℕ} (E : Fin p → Fin h → ℕ) (G : Mat 𝕋 d h)
    (a : Fin p → ℝ) (E' : Fin p → Fin (PolyZonotope.repKeep E).card → ℕ)
    (hE' : ∀ k j, E' k j = E k (PolyZonotope.keepIdx E j)) (i : Fin d) :
    (∑ l, toReal (G i l) * Real.PolyZonotope.monomial E a l)
      = ∑ j : Fin (PolyZonotope.repKeep E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
              (fun l => toReal (G i l)) (PolyZonotope.keepIdx E j)
            * Real.PolyZonotope.monomial E' a j := by
  have hmon : ∀ j, Real.PolyZonotope.monomial E' a j
      = Real.PolyZonotope.monomial E a (PolyZonotope.keepIdx E j) := fun j => by
    rw [Real.PolyZonotope.monomial, Real.PolyZonotope.monomial]
    exact Finset.prod_congr rfl fun k _ => by rw [hE' k j]
  -- the merge itself is the exact layer's, the stored columns being exact reals
  calc (∑ l, toReal (G i l) * Real.PolyZonotope.monomial E a l)
      = ∑ l, Real.PolyZonotope.monomial E a l • toReal (G i l) :=
        Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul]; exact mul_comm _ _
    _ = ∑ j ∈ PolyZonotope.repKeep E, Real.PolyZonotope.monomial E a j
          • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
              (fun l => toReal (G i l)) j :=
        Real.PolyZonotope.sum_monomial_merge E (fun l => toReal (G i l)) a
          (Real.PolyZonotope.rep E) (PolyZonotope.repKeep E)
          (Real.PolyZonotope.col_rep E)
          fun j hj => PolyZonotope.fiber_eq_zero_of_notMem E _ hj
    -- and re-indexed by a plain count, which is what the count field takes
    _ = ∑ j : Fin (PolyZonotope.repKeep E).card,
          Real.PolyZonotope.monomial E a (PolyZonotope.keepIdx E j)
            • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
                (fun l => toReal (G i l)) (PolyZonotope.keepIdx E j) :=
        ConPolyZono.aux_sum_keep _ _
    _ = ∑ j : Fin (PolyZonotope.repKeep E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E)
              (fun l => toReal (G i l)) (PolyZonotope.keepIdx E j)
            * Real.PolyZonotope.monomial E' a j :=
        Finset.sum_congr rfl fun j _ => by
          rw [smul_eq_mul, hmon j]; exact mul_comm _ _

/-! ## The generators -/

/-- A merged generator column is off by at most the gap between the two directed
masked sums. -/
theorem ConPolyZono.aux_compactGensGap (C : ConPolyZono 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep C.E).card) :
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.E)
        (fun l => toReal (C.G i l)) (PolyZonotope.keepIdx C.E j)
      - toReal (C.mergedCol i j)| ≤ toReal (ConPolyZono.compactGensGap C i j) := by
  have hlo : toReal (C.mergedCol i j)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.E)
          (fun l => toReal (C.G i l)) (PolyZonotope.keepIdx C.E j) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep C.E) C.G i (PolyZonotope.keepIdx C.E j)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.E)
        (fun l => toReal (C.G i l)) (PolyZonotope.keepIdx C.E j)
      ≤ toReal (C.mergedColUp i j) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep C.E) C.G i (PolyZonotope.keepIdx C.E j)
  have hgap := sub_le_subUp (C.mergedColUp i j) (C.mergedCol i j)
  rw [abs_le]
  simp only [ConPolyZono.compactGensGap]
  constructor <;> linarith

-- the merged column is stored downward, and that gap is what the box pays for
theorem ConPolyZono.aux_compactGens_nominal (C : ConPolyZono 𝕋 n) :
    nominalSet C ⊆ nominalSet C.compactGens
      + (PolyZonotope.generatorError (ConPolyZono.compactGensGap C)).construct := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hsat, hxi⟩ := ConPolyZono.mem_nominalSet_iff.mp hx
  refine ⟨fun i => toReal (C.c i)
            + (∑ j : Fin (PolyZonotope.repKeep C.E).card, toReal (C.mergedCol i j)
                * Real.PolyZonotope.monomial (fun k j' => C.E k (PolyZonotope.keepIdx C.E j')) a j)
            + ∑ j, toReal (C.GI i j) * β j,
          ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, hsat, fun _ => rfl⟩,
          _, PolyZonotope.mem_generatorError_monomial
            (E := fun k j' => C.E k (PolyZonotope.keepIdx C.E j'))
            (C.aux_compactGensGap) ha, ?_⟩
  funext i
  -- the stored merged columns and their errors recombine into the exact fibres
  have hsum : (∑ j : Fin (PolyZonotope.repKeep C.E).card, toReal (C.mergedCol i j)
        * Real.PolyZonotope.monomial (fun k j' => C.E k (PolyZonotope.keepIdx C.E j')) a j)
      + (∑ j : Fin (PolyZonotope.repKeep C.E).card,
          (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.E)
              (fun l => toReal (C.G i l)) (PolyZonotope.keepIdx C.E j)
            - toReal (C.mergedCol i j))
            * Real.PolyZonotope.monomial (fun k j' => C.E k (PolyZonotope.keepIdx C.E j')) a j)
      = ∑ j : Fin (PolyZonotope.repKeep C.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.E)
              (fun l => toReal (C.G i l)) (PolyZonotope.keepIdx C.E j)
            * Real.PolyZonotope.monomial (fun k j' => C.E k (PolyZonotope.keepIdx C.E j')) a j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so `hsum` and `aux_merge` line up with it
  show toReal (C.c i)
        + (∑ j : Fin (PolyZonotope.repKeep C.E).card, toReal (C.mergedCol i j)
            * Real.PolyZonotope.monomial (fun k j' => C.E k (PolyZonotope.keepIdx C.E j')) a j)
        + (∑ j, toReal (C.GI i j) * β j)
      + ∑ j : Fin (PolyZonotope.repKeep C.E).card,
          (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.E)
              (fun l => toReal (C.G i l)) (PolyZonotope.keepIdx C.E j)
            - toReal (C.mergedCol i j))
            * Real.PolyZonotope.monomial (fun k j' => C.E k (PolyZonotope.keepIdx C.E j')) a j
    = x i
  rw [hxi i, ConPolyZono.aux_merge C.E C.G a
    (fun k j' => C.E k (PolyZonotope.keepIdx C.E j')) (fun _ _ => rfl) i]
  linarith [hsum]

theorem ConPolyZono.compactGens_outer (C : ConPolyZono 𝕋 n) :
    C.construct ⊆ C.compactGens.construct := by
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', d, hd, hsum⟩ := ConPolyZono.aux_compactGens_nominal C hz
  refine ⟨z', hz', e + d, Interval.plus_outer _ _ ⟨e, he, d, hd, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + d = z := hsum
  show z' + (e + d) = z + e
  rw [← hsum', add_comm e d, ← add_assoc]

/-! ## The constraints -/

/-- A merged constraint column is off by at most the gap between the two
directed masked sums, as a generator column is. -/
theorem ConPolyZono.aux_compactConsGap (C : ConPolyZono 𝕋 n) (i : Fin C.m)
    (l : Fin (PolyZonotope.repKeep C.EC).card) :
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.EC)
        (fun r => toReal (C.A i r)) (PolyZonotope.keepIdx C.EC l)
      - toReal (C.mergedConsCol i l)| ≤ toReal (ConPolyZono.compactConsGap C i l) := by
  have hlo : toReal (C.mergedConsCol i l)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.EC)
          (fun r => toReal (C.A i r)) (PolyZonotope.keepIdx C.EC l) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep C.EC) C.A i (PolyZonotope.keepIdx C.EC l)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.EC)
        (fun r => toReal (C.A i r)) (PolyZonotope.keepIdx C.EC l)
      ≤ toReal (C.mergedConsColUp i l) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep C.EC) C.A i (PolyZonotope.keepIdx C.EC l)
  have hgap := sub_le_subUp (C.mergedConsColUp i l) (C.mergedConsCol i l)
  rw [abs_le]
  simp only [ConPolyZono.compactConsGap]
  constructor <;> linarith

/-- The widened bound admits every factor vector the old one did: the row moved
by at most one `radius` of its gaps, and `b` moved out by exactly that. -/
theorem ConPolyZono.aux_satisfies_compactCons (C : ConPolyZono 𝕋 n) {a : Fin C.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (hsat : C.satisfies a) : C.compactCons.satisfies a := by
  intro i
  have hb : toReal (C.b.inf i)
        ≤ (∑ l, toReal (C.A i l) * Real.PolyZonotope.monomial C.EC a l)
      ∧ (∑ l, toReal (C.A i l) * Real.PolyZonotope.monomial C.EC a l)
        ≤ toReal (C.b.sup i) := hsat i
  have hex := ConPolyZono.aux_merge C.EC C.A a
    (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) (fun _ _ => rfl) i
  -- the exact merged row is the stored one plus what the gaps carry
  have hsplit : (∑ j, Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.EC)
            (fun r => toReal (C.A i r)) (PolyZonotope.keepIdx C.EC j)
          * Real.PolyZonotope.monomial
              (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) a j)
      = (∑ j, toReal (C.mergedConsCol i j)
            * Real.PolyZonotope.monomial
                (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) a j)
        + ∑ j, (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.EC)
              (fun r => toReal (C.A i r)) (PolyZonotope.keepIdx C.EC j)
            - toReal (C.mergedConsCol i j))
            * Real.PolyZonotope.monomial
                (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) a j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- one radius bounds the whole row, every constraint monomial lying in `[-1,1]`
  have hrad : |∑ j, (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.EC)
              (fun r => toReal (C.A i r)) (PolyZonotope.keepIdx C.EC j)
            - toReal (C.mergedConsCol i j))
            * Real.PolyZonotope.monomial
                (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) a j|
      ≤ toReal (radius (ConPolyZono.compactConsGap C) i) :=
    abs_sum_le_radius
      (Δ := fun i j => Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep C.EC)
              (fun r => toReal (C.A i r)) (PolyZonotope.keepIdx C.EC j)
            - toReal (C.mergedConsCol i j))
      (fun i j => le_trans (ConPolyZono.aux_compactConsGap C i j) (le_abs_self _))
      (fun j => Real.PolyZonotope.abs_monomial_le_one
        (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) ha j) i
  rw [abs_le] at hrad
  -- both bounds now, `b` having moved out by the very number `hrad` supplies
  refine ⟨?_, ?_⟩
  · show toReal (subDown (C.b.inf i) (radius (ConPolyZono.compactConsGap C) i))
      ≤ ∑ j, toReal (C.mergedConsCol i j)
          * Real.PolyZonotope.monomial
              (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) a j
    have hd := subDown_le_sub (C.b.inf i) (radius (ConPolyZono.compactConsGap C) i)
    linarith [hb.1, hex, hsplit, hrad.1, hrad.2]
  · show (∑ j, toReal (C.mergedConsCol i j)
          * Real.PolyZonotope.monomial
              (fun k j' => C.EC k (PolyZonotope.keepIdx C.EC j')) a j)
      ≤ toReal (addUp (C.b.sup i) (radius (ConPolyZono.compactConsGap C) i))
    have hu := add_le_addUp (C.b.sup i) (radius (ConPolyZono.compactConsGap C) i)
    linarith [hb.2, hex, hsplit, hrad.1, hrad.2]

/-- Only the constraint weakens, so the nominal set grows and the error box does
not move. -/
theorem ConPolyZono.aux_compactCons_nominal (C : ConPolyZono 𝕋 n) :
    nominalSet C ⊆ nominalSet C.compactCons := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hsat, hxi⟩ := ConPolyZono.mem_nominalSet_iff.mp hx
  exact ConPolyZono.mem_nominalSet_iff.mpr
    ⟨a, β, ha, hβ, ConPolyZono.aux_satisfies_compactCons C ha hsat, hxi⟩

theorem ConPolyZono.compactCons_outer (C : ConPolyZono 𝕋 n) :
    C.construct ⊆ C.compactCons.construct :=
  InflatedContSet.mono_subset (ConPolyZono.aux_compactCons_nominal C) (subset_refl _)

/-! ## The factors -/

/-- Dropping unused factors is the exact layer's step verbatim: the nominal part
of the result is `compactFactors` of the nominal part. -/
theorem ConPolyZono.compactFactors_nominal (C : ConPolyZono 𝕋 n) :
    nominalSet C = nominalSet C.compactFactors :=
  Real.ConPolyZono.compactFactors_exact (InflatedContSet.nominal C)

theorem ConPolyZono.compactFactors_outer (C : ConPolyZono 𝕋 n) :
    C.construct ⊆ C.compactFactors.construct :=
  InflatedContSet.mono_subset (ConPolyZono.compactFactors_nominal C).subset (subset_refl _)

theorem ConPolyZono.compact_outer (C : ConPolyZono 𝕋 n) :
    C.construct ⊆ C.compact.construct :=
  subset_trans (ConPolyZono.compactGens_outer C)
    (subset_trans (ConPolyZono.compactCons_outer C.compactGens)
      (ConPolyZono.compactFactors_outer C.compactGens.compactCons))

end CORALean.Float
