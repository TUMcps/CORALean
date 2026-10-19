module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberEqZeroOfNotMem
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `compactGens` over-approximates, merging generator columns

Adding the entries of a class rounds, so the exact fibre sum is bracketed by
the two directed masked sums, the lower is stored, and the gap is a
`generatorError` — the merged column's coefficient being a monomial in
`[-1,1]`. `sum_monomial_merge` is the exact layer's and knows nothing about a
scalar.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over the kept columns, read against a plain count. -/
theorem PolyZonotope.aux_sum_keep (s : Finset (Fin h)) (f : Fin h → ℝ) :
    ∑ j ∈ s, f j = ∑ j : Fin s.card, f (s.orderIsoOfFin rfl j) := by
  rw [← Finset.sum_coe_sort s f]
  exact (Equiv.sum_comp (s.orderIsoOfFin rfl).toEquiv fun x => f x).symm

/-- The exact layer's regrouping at this layer's stored generators, the merged
columns still exact reals. -/
theorem PolyZonotope.aux_merge (pZ : PolyZonotope (Vec 𝕋 n)) (a : Fin pZ.p → ℝ)
    (i : Fin n) : -- --- CONCL ---
    (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
      = ∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E)
              (fun l => toReal (pZ.G l i)) (PolyZonotope.keepIdx pZ.E j)
            * Real.PolyZonotope.monomial pZ.compactGens.E a j := by -- --- PROOF ---
  -- the merge is the exact layer's, the stored columns being exact reals here
  calc (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
      = ∑ l, Real.PolyZonotope.monomial pZ.E a l • toReal (pZ.G l i) :=
        Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul]; exact mul_comm _ _
    _ = ∑ j ∈ PolyZonotope.repKeep pZ.E, Real.PolyZonotope.monomial pZ.E a j
          • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E)
              (fun l => toReal (pZ.G l i)) j :=
        Real.PolyZonotope.sum_monomial_merge pZ.E (fun l => toReal (pZ.G l i)) a
          (Real.PolyZonotope.rep pZ.E) (PolyZonotope.repKeep pZ.E)
          (Real.PolyZonotope.col_rep pZ.E)
          fun j hj => PolyZonotope.fiber_eq_zero_of_notMem pZ.E _ hj
    _ = ∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          Real.PolyZonotope.monomial pZ.E a (PolyZonotope.keepIdx pZ.E j)
            • Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E)
                (fun l => toReal (pZ.G l i)) (PolyZonotope.keepIdx pZ.E j) :=
        PolyZonotope.aux_sum_keep _ _
    _ = ∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E)
              (fun l => toReal (pZ.G l i)) (PolyZonotope.keepIdx pZ.E j)
            * Real.PolyZonotope.monomial pZ.compactGens.E a j :=
        Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]; exact mul_comm _ _

/-- A merged column is off by at most the gap between the two directed masked
sums. -/
theorem PolyZonotope.aux_compactGap (pZ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep pZ.E).card) : -- --- CONCL ---
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E)
        (fun l => toReal (pZ.G l i)) (PolyZonotope.keepIdx pZ.E j)
      - toReal (pZ.mergedCol i j)| ≤ toReal (PolyZonotope.compactGap pZ i j) := by -- --- PROOF ---
  have hlo : toReal (pZ.mergedCol i j)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E)
          (fun l => toReal (pZ.G l i)) (PolyZonotope.keepIdx pZ.E j) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep pZ.E) (fun i l => pZ.G l i) i
      (PolyZonotope.keepIdx pZ.E j)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E)
        (fun l => toReal (pZ.G l i)) (PolyZonotope.keepIdx pZ.E j)
      ≤ toReal (pZ.mergedColUp i j) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep pZ.E) (fun i l => pZ.G l i) i
      (PolyZonotope.keepIdx pZ.E j)
  have hgap := sub_le_subUp (pZ.mergedColUp i j) (pZ.mergedCol i j)
  rw [abs_le]
  simp only [PolyZonotope.compactGap]
  constructor <;> linarith

-- the merged column is stored downward, and that gap is what the box pays for
theorem PolyZonotope.aux_compactGens_nominal (pZ : PolyZonotope (Vec 𝕋 n)) :
    nominalSet pZ ⊆ nominalSet pZ.compactGens
      + (PolyZonotope.generatorError (PolyZonotope.compactGap pZ)).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  -- the monomials on the kept exponents, and the exact fibre sums of coordinate `i`
  set mon := Real.PolyZonotope.monomial pZ.compactGens.E a
  set fib : Fin n → Fin (PolyZonotope.repKeep pZ.E).card → ℝ := fun i j =>
    Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E) (fun l => toReal (pZ.G l i))
      (PolyZonotope.keepIdx pZ.E j)
  refine ⟨fun i => toReal (pZ.c i)
            + (∑ j : Fin (PolyZonotope.repKeep pZ.E).card, toReal (pZ.mergedCol i j) * mon j)
            + ∑ j, toReal (pZ.GI j i) * β j,
          PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩,
          _, PolyZonotope.mem_generatorError_monomial (E := pZ.compactGens.E)
            (pZ.aux_compactGap) ha, ?_⟩
  funext i
  -- the stored merged columns and their errors recombine into the exact fibres
  have hsum : (∑ j : Fin (PolyZonotope.repKeep pZ.E).card, toReal (pZ.mergedCol i j) * mon j)
      + (∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          (fib i j - toReal (pZ.mergedCol i j)) * mon j)
      = ∑ j : Fin (PolyZonotope.repKeep pZ.E).card, fib i j * mon j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so `hsum` and `aux_merge` line up with it
  show toReal (pZ.c i)
        + (∑ j : Fin (PolyZonotope.repKeep pZ.E).card, toReal (pZ.mergedCol i j) * mon j)
        + (∑ j, toReal (pZ.GI j i) * β j)
      + ∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          (fib i j - toReal (pZ.mergedCol i j)) * mon j
    = x i
  rw [hxi i, PolyZonotope.aux_merge pZ a i]
  linarith [hsum]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compactGens_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.compactGens.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', d, hd, hsum⟩ := PolyZonotope.aux_compactGens_nominal pZ hz
  refine ⟨z', hz', e + d, Interval.plus_outer _ _ ⟨e, he, d, hd, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + d = z := hsum
  show z' + (e + d) = z + e
  rw [← hsum', add_comm e d, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
