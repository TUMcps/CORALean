import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConPolyZono.Float.Theorems.Merge
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial

/-!
# `compactGens` over-approximates, merging generator columns

A merged generator column is bracketed by the two directed masked sums, the
lower is stored, and the gap is a `generatorError` in the ambient box. The
nominal set only *grows* at this stage, and the error box does not move.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- A merged generator column is off by at most the gap between the two
directed masked sums. -/
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
  rw [hxi i, ConPolyZono.merge C.E C.G a
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

end CORALean.Float
