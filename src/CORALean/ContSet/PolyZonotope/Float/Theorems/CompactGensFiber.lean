module

public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberEqZeroOfNotMem
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial

@[expose] public section

/-!
# `compactGens` keeps every fiber, merging generator columns

Adding the entries of a class rounds, so the exact fibre sum is bracketed by
the two directed masked sums, the lower is stored, and the gap is a
`generatorError` — the merged column's coefficient being a monomial in
`[-1,1]`. `sum_monomial_merge` is the exact layer's and knows nothing about a
scalar. The factor values stay, so the statement serves the set as well as the fibers.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values
* `x` – point

## Hypotheses
* `ha` – the factor values lie in the unit box
* `hx` – the point is in the fiber of `pZ` at `a`

## Conclusion
* the point is in the fiber of the result at `a`
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over the kept columns, read against a plain count. -/
private theorem PolyZonotope.aux_sum_keep (s : Finset (Fin h)) (f : Fin h → ℝ) :
    ∑ j ∈ s, f j = ∑ j : Fin s.card, f (s.orderIsoOfFin rfl j) := by
  rw [← Finset.sum_coe_sort s f]
  exact (Equiv.sum_comp (s.orderIsoOfFin rfl).toEquiv fun x => f x).symm

/-- The exact layer's regrouping at this layer's stored generators, the merged
columns still exact reals. -/
private theorem PolyZonotope.aux_merge (pZ : PolyZonotope (Vec 𝕋 n)) (a : Fin pZ.p → ℝ)
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
private theorem PolyZonotope.aux_compactGap (pZ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging equal exponent columns keeps the fiber at every factor value: the merged column is
stored downward, and the gap is a point of the box. -/
theorem PolyZonotope.compactGens_fiber (pZ : PolyZonotope (Vec 𝕋 n)) {a : Fin pZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) {x : Vec ℝ n} (hx : x ∈ pZ.fiber a) : -- --- CONCL ---
    x ∈ pZ.compactGens.fiber a := by -- --- PROOF ---
  -- the point at the factors `a`, and the gap a merged column adds to the box
  obtain ⟨β, hβ, e, he, hxe⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
  obtain ⟨d, hd, hdd⟩ : ∃ d ∈ (PolyZonotope.generatorError (PolyZonotope.compactGap pZ)).toSet,
      d = fun i => ∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
        (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E) (fun l => toReal (pZ.G l i))
          (PolyZonotope.keepIdx pZ.E j) - toReal (pZ.mergedCol i j))
          * Real.PolyZonotope.monomial pZ.compactGens.E a j :=
    ⟨_, PolyZonotope.mem_generatorError_monomial (E := pZ.compactGens.E)
      (pZ.aux_compactGap) ha, rfl⟩
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨β, hβ, e + d,
    Interval.plus_outer _ _ ⟨e, he, d, hd, rfl⟩, ?_⟩
  -- the merged columns against the exact fibre sums, coordinate by coordinate
  rw [hxe, hdd]
  funext i
  repeat rw [PolyZonotope.nominal_point_eq]
  simp only [Pi.add_apply]
  have hsum : (∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
        toReal (pZ.mergedCol i j) * Real.PolyZonotope.monomial pZ.compactGens.E a j)
      + (∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E) (fun l => toReal (pZ.G l i))
            (PolyZonotope.keepIdx pZ.E j) - toReal (pZ.mergedCol i j))
            * Real.PolyZonotope.monomial pZ.compactGens.E a j)
      = ∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep pZ.E) (fun l => toReal (pZ.G l i))
            (PolyZonotope.keepIdx pZ.E j) * Real.PolyZonotope.monomial pZ.compactGens.E a j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the exact layer's regrouping closes the goal
  have hm := PolyZonotope.aux_merge pZ a i
  show toReal (pZ.c i) + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l
      + ∑ j, toReal (pZ.GI j i) * β j + e i = toReal (pZ.c i)
        + (∑ j : Fin (PolyZonotope.repKeep pZ.E).card,
          toReal (pZ.mergedCol i j) * Real.PolyZonotope.monomial pZ.compactGens.E a j)
      + ∑ j, toReal (pZ.GI j i) * β j + (e i + _)
  rw [hm]
  linarith [hsum]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
