import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsGap
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsColUp
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactConsEqSpec
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConPolyZono.Float.Theorems.Merge
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

/-!
# `compactCons` over-approximates, merging constraint rows

A merged constraint row has no ambient box to reach, so `b` absorbs it:
`abs_sum_le_radius` turns the row of gaps into one bound, the constraint
monomials being in `[-1,1]`, and the bound moves out by it on both sides. The
nominal set only *grows*, and the error box does not move.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A merged constraint column is off by at most the gap between the two
directed masked sums, as a generator column is. -/
theorem ConPolyZono.aux_compactConsGap (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin cPZ.m)
    (l : Fin (PolyZonotope.repKeep cPZ.EC).card) :
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.EC)
        (fun r => toReal (cPZ.A i r)) (PolyZonotope.keepIdx cPZ.EC l)
      - toReal (cPZ.mergedConsCol i l)|
        ≤ toReal (ConPolyZono.compactConsGap cPZ i l) := by -- --- PROOF ---
  have hlo : toReal (cPZ.mergedConsCol i l)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.EC)
          (fun r => toReal (cPZ.A i r)) (PolyZonotope.keepIdx cPZ.EC l) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep cPZ.EC) cPZ.A i (PolyZonotope.keepIdx cPZ.EC l)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.EC)
        (fun r => toReal (cPZ.A i r)) (PolyZonotope.keepIdx cPZ.EC l)
      ≤ toReal (cPZ.mergedConsColUp i l) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep cPZ.EC) cPZ.A i (PolyZonotope.keepIdx cPZ.EC l)
  have hgap := sub_le_subUp (cPZ.mergedConsColUp i l) (cPZ.mergedConsCol i l)
  rw [abs_le]
  simp only [ConPolyZono.compactConsGap]
  constructor <;> linarith

/-- The widened bound admits every factor vector the old one did: the row moved
by at most one `radius` of its gaps, and `b` moved out by exactly that. -/
theorem ConPolyZono.aux_satisfies_compactCons (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {a : Fin cPZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (hsat : cPZ.satisfies a) :
    cPZ.compactConsSpec.satisfies a := by -- --- PROOF ---
  intro i
  have hb : toReal (cPZ.b.inf i)
        ≤ (∑ l, toReal (cPZ.A i l) * Real.PolyZonotope.monomial cPZ.EC a l)
      ∧ (∑ l, toReal (cPZ.A i l) * Real.PolyZonotope.monomial cPZ.EC a l)
        ≤ toReal (cPZ.b.sup i) := hsat i
  have hex := ConPolyZono.merge cPZ.EC cPZ.A a
    (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) (fun _ _ => rfl) i
  -- the exact merged row is the stored one plus what the gaps carry
  have hsplit : (∑ j, Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.EC)
            (fun r => toReal (cPZ.A i r)) (PolyZonotope.keepIdx cPZ.EC j)
          * Real.PolyZonotope.monomial
              (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) a j)
      = (∑ j, toReal (cPZ.mergedConsCol i j)
            * Real.PolyZonotope.monomial
                (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) a j)
        + ∑ j, (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.EC)
              (fun r => toReal (cPZ.A i r)) (PolyZonotope.keepIdx cPZ.EC j)
            - toReal (cPZ.mergedConsCol i j))
            * Real.PolyZonotope.monomial
                (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) a j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- one radius bounds the whole row, every constraint monomial lying in `[-1,1]`
  have hrad : |∑ j, (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.EC)
              (fun r => toReal (cPZ.A i r)) (PolyZonotope.keepIdx cPZ.EC j)
            - toReal (cPZ.mergedConsCol i j))
            * Real.PolyZonotope.monomial
                (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) a j|
      ≤ toReal (radius (ConPolyZono.compactConsGap cPZ) i) :=
    abs_sum_le_radius
      (Δ := fun i j => Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.EC)
              (fun r => toReal (cPZ.A i r)) (PolyZonotope.keepIdx cPZ.EC j)
            - toReal (cPZ.mergedConsCol i j))
      (fun i j => le_trans (ConPolyZono.aux_compactConsGap cPZ i j) (le_abs_self _))
      (fun j => Real.PolyZonotope.abs_monomial_le_one
        (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) ha j) i
  rw [abs_le] at hrad
  -- both bounds now, `b` having moved out by the very number `hrad` supplies
  refine ⟨?_, ?_⟩
  · show toReal (subDown (cPZ.b.inf i) (radius (ConPolyZono.compactConsGap cPZ) i))
      ≤ ∑ j, toReal (cPZ.mergedConsCol i j)
          * Real.PolyZonotope.monomial
              (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) a j
    have hd := subDown_le_sub (cPZ.b.inf i) (radius (ConPolyZono.compactConsGap cPZ) i)
    linarith [hb.1, hex, hsplit, hrad.1, hrad.2]
  · show (∑ j, toReal (cPZ.mergedConsCol i j)
          * Real.PolyZonotope.monomial
              (fun k j' => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC j')) a j)
      ≤ toReal (addUp (cPZ.b.sup i) (radius (ConPolyZono.compactConsGap cPZ) i))
    have hu := add_le_addUp (cPZ.b.sup i) (radius (ConPolyZono.compactConsGap cPZ) i)
    linarith [hb.2, hex, hsplit, hrad.1, hrad.2]

/-- Only the constraint weakens, so the nominal set grows and the error box does
not move. -/
theorem ConPolyZono.aux_compactCons_nominal (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    nominalSet cPZ ⊆ nominalSet cPZ.compactConsSpec := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hsat, hxi⟩ := ConPolyZono.mem_nominalSet_iff.mp hx
  exact ConPolyZono.mem_nominalSet_iff.mpr
    ⟨a, β, ha, hβ, ConPolyZono.aux_satisfies_compactCons cPZ ha hsat, hxi⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactCons_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.compactCons.construct := by
  rw [ConPolyZono.compactCons_eq_spec]
  exact InflatedContSet.mono_subset (ConPolyZono.aux_compactCons_nominal cPZ) (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
