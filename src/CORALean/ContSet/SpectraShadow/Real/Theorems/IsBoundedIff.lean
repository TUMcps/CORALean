module

public import CORALean.ContSet.SpectraShadow.Real.Operations.IsBounded
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncNeTopIff

@[expose] public section

/-!
# `SpectraShadow.isBounded` is boundedness

The `2n` coordinate support values are finite exactly when the set is bounded: a real bound on
each coordinate from above and below is a bound on the sup norm, and conversely. So CORA's test
decides boundedness, up to the solver and the all-`Aᵢ`-zero shortcut of
`references/coverage/contSet/spectraShadow.md`, row `isBounded`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.isBounded_iff (S : SpectraShadow (Vec ℝ n)) :
    S.isBounded ↔ Bornology.IsBounded S.construct := by -- --- PROOF ---
  rw [isBounded_iff_forall_norm_le]
  constructor
  · -- real bounds `Mp i`, `Mm i` on each coordinate, summed into a bound on the sup norm
    intro h
    choose hp hm using h
    choose Mp hMp using fun i => (S.supportFunc_ne_top_iff _).mp (hp i)
    choose Mm hMm using fun i => (S.supportFunc_ne_top_iff _).mp (hm i)
    refine ⟨∑ i, (|Mp i| + |Mm i|), fun x hx => ?_⟩
    have hC : 0 ≤ ∑ i, (|Mp i| + |Mm i|) :=
      Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    refine (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_
    have h1 := hMp i x hx
    have h2 := hMm i x hx
    simp only [LinearMap.proj_apply, LinearMap.neg_apply] at h1 h2
    have h3 : |Mp i| + |Mm i| ≤ ∑ i, (|Mp i| + |Mm i|) :=
      Finset.single_le_sum (f := fun i => |Mp i| + |Mm i|)
        (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [le_abs_self (Mp i), le_abs_self (Mm i), abs_nonneg (Mp i),
      abs_nonneg (Mm i)]
  · -- a bound on the norm bounds each coordinate, from both sides
    rintro ⟨C, hC⟩ i
    constructor <;> rw [SpectraShadow.supportFunc_ne_top_iff]
    · exact ⟨C, fun x hx => by
        simpa using (le_abs_self (x i)).trans ((norm_le_pi_norm x i).trans (hC x hx))⟩
    · exact ⟨C, fun x hx => by
        simpa using (neg_le_abs (x i)).trans ((norm_le_pi_norm x i).trans (hC x hx))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
