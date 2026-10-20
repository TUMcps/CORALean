module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBox
public import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalOnMono
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByEvalOn
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# CORA's `reduce` preserves dependencies, up to the factors it drops

[1] leaves order reduction out of its Table 1, so nothing says the reducing step of its Alg. 1
is dependency preserving, which [1, Lemma 4] needs; this says it. Both halves of `reduce`
answer at the very same factor values (`compactGens` merges columns, `reduceBy` boxes
generators into the *independent* block), so only `compactFactors` moves anything, renumbering
the factors still read. The target box is therefore stated index by index: `factorIdx` is the
order embedding of the surviving factors, and a factor vector carries over by reading it so.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order
* `B` – box of factor values

## Hypotheses
* `hB` – factor values are at most one

## Conclusion
* evaluation on the box lies in the reduced evaluation on the mapped box

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `compactGens`'s regrouping of the dependent sum, at one factor vector. -/
theorem PolyZonotope.aux_compactGens_sum (pZ : PolyZonotope (Vec ℝ n))
    (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ j : Fin pZ.compactGens.h,
          PolyZonotope.monomial pZ.compactGens.E a j • pZ.compactGens.G j := by -- --- PROOF ---
  rw [PolyZonotope.sum_monomial_merge pZ.E pZ.G a (PolyZonotope.rep pZ.E)
      (PolyZonotope.compactKeep pZ.E pZ.G) (PolyZonotope.col_rep pZ.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem pZ.E pZ.G hj,
    PolyZonotope.sum_compactKeep]
  rfl

/-- `compactFactors`'s same sum, read against the factors it keeps. -/
theorem PolyZonotope.aux_compactFactors_sum (pZ : PolyZonotope (Vec ℝ n))
    (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ i : Fin pZ.compactFactors.h, PolyZonotope.monomial pZ.compactFactors.E
          (fun k => a (PolyZonotope.factorIdx pZ.E k)) i
            • pZ.compactFactors.G i := by -- --- PROOF ---
  -- the binder read back at `pZ.h`, which is what `monomial_factorIdx` is stated over
  show (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ i : Fin pZ.h,
          PolyZonotope.monomial (fun k i => pZ.E (PolyZonotope.factorIdx pZ.E k) i)
            (fun k => a (PolyZonotope.factorIdx pZ.E k)) i • pZ.G i
  exact Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_factorIdx]

/-- `compact` keeps the point it denotes, read through the renumbering of the
factors it still uses. -/
theorem PolyZonotope.aux_compact_point (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ) :
    pZ.compact.point (fun k => a (PolyZonotope.factorIdx pZ.compactGens.E k))
      = pZ.point a :=
  congrArg (pZ.c + ·) ((PolyZonotope.aux_compactFactors_sum pZ.compactGens a).symm.trans
    (PolyZonotope.aux_compactGens_sum pZ a).symm)

/-- `compact` evaluated at the carried factor vector, which is the whole of what
the merging and the dropping of factors do to a dependency. -/
theorem PolyZonotope.aux_compact_evalOn (pZ : PolyZonotope (Vec ℝ n))
    {B : Set (Fin pZ.p → ℝ)} :
    pZ.evalOn B ⊆ pZ.compact.evalOn ((fun (a : Fin pZ.p → ℝ) (k : Fin pZ.compact.p) =>
      a (PolyZonotope.factorIdx pZ.compactGens.E k)) '' B) := by
  rintro _ ⟨a, haB, β, hβ, rfl⟩
  exact ⟨_, ⟨a, haB, rfl⟩, β, hβ, congrArg (· + ∑ j, β j • pZ.GI j)
    (PolyZonotope.aux_compact_point pZ a).symm⟩

/-- Girard's rule leaves the factors alone: past the order bound it boxes
generators into the independent block, below it nothing happens. -/
theorem PolyZonotope.aux_reduceGirard_evalOn (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ)
    {B : Set (Fin pZ.p → ℝ)} (hB : ∀ a ∈ B, ∀ k, |a k| ≤ 1) : -- --- CONCL ---
    pZ.evalOn B ⊆ (pZ.reduceGirard o).evalOn
      {a' | ∃ a ∈ B, ∀ (k : Fin (pZ.reduceGirard o).p) (k' : Fin pZ.p),
        (k : ℕ) = (k' : ℕ) → a' k = a k'} := by -- --- PROOF ---
  rw [PolyZonotope.reduceGirard]
  by_cases hc : o * n < pZ.h + pZ.q
  · rw [if_pos hc]
    exact (PolyZonotope.reduceBy_evalOn pZ _ _ hB).trans (PolyZonotope.evalOn_mono _
      fun a ha => ⟨a, ha, fun k k' hk => congrArg a (Fin.eq_of_val_eq hk)⟩)
  · rw [if_neg hc]
    exact PolyZonotope.evalOn_mono _
      fun a ha => ⟨a, ha, fun k k' hk => congrArg a (Fin.eq_of_val_eq hk)⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every evaluation of `pZ` lies inside the evaluation of its reduction at the
factor vector `factorIdx` carries across. -/
theorem PolyZonotope.reduce_evalOn (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ)
    {B : Set (Fin pZ.p → ℝ)} (hB : ∀ a ∈ B, ∀ k, |a k| ≤ 1) : -- --- CONCL ---
    pZ.evalOn B ⊆ (pZ.reduce o).evalOn (PolyZonotope.reduceBox pZ o B) := by -- --- PROOF ---
  refine (PolyZonotope.aux_compact_evalOn pZ).trans
    ((PolyZonotope.aux_reduceGirard_evalOn pZ.compact o ?_).trans
      (PolyZonotope.evalOn_mono _ ?_))
  · rintro _ ⟨a, haB, rfl⟩ k
    exact hB a haB _
  -- the carried vector, read back through the image the first step left
  · rintro a' ⟨_, ⟨a, haB, rfl⟩, hcarry⟩
    exact ⟨a, haB, hcarry⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
