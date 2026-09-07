import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGens
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensGap
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedColUp
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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A merged generator column is off by at most the gap between the two
directed masked sums. -/
theorem ConPolyZono.aux_compactGensGap (cPZ : ConPolyZono 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep cPZ.E).card) :
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.E)
        (fun l => toReal (cPZ.G i l)) (PolyZonotope.keepIdx cPZ.E j)
      - toReal (cPZ.mergedCol i j)|
    ≤ toReal (ConPolyZono.compactGensGap cPZ i j) := by -- --- PROOF ---
  have hlo : toReal (cPZ.mergedCol i j)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.E)
          (fun l => toReal (cPZ.G i l)) (PolyZonotope.keepIdx cPZ.E j) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep cPZ.E) cPZ.G i (PolyZonotope.keepIdx cPZ.E j)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.E)
        (fun l => toReal (cPZ.G i l)) (PolyZonotope.keepIdx cPZ.E j)
      ≤ toReal (cPZ.mergedColUp i j) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep cPZ.E) cPZ.G i (PolyZonotope.keepIdx cPZ.E j)
  have hgap := sub_le_subUp (cPZ.mergedColUp i j) (cPZ.mergedCol i j)
  rw [abs_le]
  simp only [ConPolyZono.compactGensGap]
  constructor <;> linarith

-- the merged column is stored downward, and that gap is what the box pays for
theorem ConPolyZono.aux_compactGens_nominal (cPZ : ConPolyZono 𝕋 n) :
    nominalSet cPZ ⊆ nominalSet cPZ.compactGens
      + (PolyZonotope.generatorError
        (ConPolyZono.compactGensGap cPZ)).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, β, ha, hβ, hsat, hxi⟩ := ConPolyZono.mem_nominalSet_iff.mp hx
  refine ⟨fun i => toReal (cPZ.c i)
            + (∑ j : Fin (PolyZonotope.repKeep cPZ.E).card, toReal (cPZ.mergedCol i j)
                * Real.PolyZonotope.monomial
                    (fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j')) a j)
            + ∑ j, toReal (cPZ.GI i j) * β j,
          ConPolyZono.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, hsat, fun _ => rfl⟩,
          _, PolyZonotope.mem_generatorError_monomial
            (E := fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j'))
            (cPZ.aux_compactGensGap) ha, ?_⟩
  funext i
  -- the stored merged columns and their errors recombine into the exact fibres
  have hsum : (∑ j : Fin (PolyZonotope.repKeep cPZ.E).card, toReal (cPZ.mergedCol i j)
        * Real.PolyZonotope.monomial (fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j')) a j)
      + (∑ j : Fin (PolyZonotope.repKeep cPZ.E).card,
          (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.E)
              (fun l => toReal (cPZ.G i l)) (PolyZonotope.keepIdx cPZ.E j)
            - toReal (cPZ.mergedCol i j))
            * Real.PolyZonotope.monomial (fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j')) a j)
      = ∑ j : Fin (PolyZonotope.repKeep cPZ.E).card,
          Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.E)
              (fun l => toReal (cPZ.G i l)) (PolyZonotope.keepIdx cPZ.E j)
            * Real.PolyZonotope.monomial
                (fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j')) a j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the goal spelled out, so `hsum` and `aux_merge` line up with it
  show toReal (cPZ.c i)
        + (∑ j : Fin (PolyZonotope.repKeep cPZ.E).card, toReal (cPZ.mergedCol i j)
            * Real.PolyZonotope.monomial (fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j')) a j)
        + (∑ j, toReal (cPZ.GI i j) * β j)
      + ∑ j : Fin (PolyZonotope.repKeep cPZ.E).card,
          (Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.E)
              (fun l => toReal (cPZ.G i l)) (PolyZonotope.keepIdx cPZ.E j)
            - toReal (cPZ.mergedCol i j))
            * Real.PolyZonotope.monomial (fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j')) a j
    = x i
  rw [hxi i, ConPolyZono.merge cPZ.E cPZ.G a
    (fun k j' => cPZ.E k (PolyZonotope.keepIdx cPZ.E j')) (fun _ _ => rfl) i]
  linarith [hsum]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactGens_outer (cPZ : ConPolyZono 𝕋 n) :
    cPZ.construct ⊆ cPZ.compactGens.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', d, hd, hsum⟩ := ConPolyZono.aux_compactGens_nominal cPZ hz
  refine ⟨z', hz', e + d, Interval.plus_outer _ _ ⟨e, he, d, hd, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + d = z := hsum
  show z' + (e + d) = z + e
  rw [← hsum', add_comm e d, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
