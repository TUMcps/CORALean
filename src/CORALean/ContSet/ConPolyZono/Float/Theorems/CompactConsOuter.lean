import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
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

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

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
  have hex := ConPolyZono.merge C.EC C.A a
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

end CORALean.Float
