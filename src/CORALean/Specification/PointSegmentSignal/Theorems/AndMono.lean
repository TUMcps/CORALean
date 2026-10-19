module

public import CORALean.Specification.PointSegmentSignal.Theorems.CombineSpec
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Bool.Basic

@[expose] public section

/-!
# The conjunction of Boolean signals is monotone

The conjunction of Boolean signals is `combine` with `@all`: if every signal is `⊑ₜ` the primed
one at every time `t ≥ 0`, so is the conjunction ([1, Sec. 4.2 (monotonicity)]).

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.and_mono {ι : Type} [Fintype ι] [Nonempty ι]
    (sigs sigs' : ι → PointSegmentSignal ℝ) (hv : ∀ k, (sigs k).IsValid)
    (hv' : ∀ k, (sigs' k).IsValid)
    (h : ∀ k, ∀ t : ℝ, 0 ≤ t → (sigs k).at t ≤ (sigs' k).at t) : -- --- CONCL ---
    ∀ t : ℝ, 0 ≤ t →
      (PointSegmentSignal.combine (fun (args : ι → Bool) (_ : Unit) => decide (∀ k, args k = true))
        sigs ()).at t ≤
      (PointSegmentSignal.combine (fun (args : ι → Bool) (_ : Unit) => decide (∀ k, args k = true))
        sigs' ()).at t := by -- --- PROOF ---
  intro t ht
  rw [(PointSegmentSignal.combine_spec _ sigs hv ()).2 t ht,
    (PointSegmentSignal.combine_spec _ sigs' hv' ()).2 t ht]
  rw [Bool.le_iff_imp]
  intro hall
  simp only [decide_eq_true_eq] at hall ⊢
  exact fun k => Bool.le_iff_imp.1 (h k t ht) (hall k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
