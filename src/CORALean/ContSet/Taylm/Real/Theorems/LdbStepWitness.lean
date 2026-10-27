module

public import CORALean.ContSet.Taylm.Real.Theorems.LdbStepReduce
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# LDB keeps a point at most `Min`

The left end and the mid-point both bound `Min` from below, one of them attaining it, and the
other estimate is above the function everywhere; the point is kept, since a cut point is above
`Min` (`ldbStep_reduce`). Why cutting loses nothing in [1, Sec. 2].

## Inputs
* `T` – Taylor model
* `g` – enclosed function

## Hypotheses
* `h` – the model encloses the function

## Conclusion
* a kept point has a value within the step's upper bound

## References

* [1] [K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.](../../../../../../references/2005/makino-tc-global-optimization.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.ldbStep_witness {T : Taylm n} {g : Vec ℝ n → ℝ} (h : T.Encloses g) : -- --- CONCL ---
    ∃ q ∈ Taylm.box n, Taylm.IsInBox T.ldbStep.2 q ∧ g q ≤ T.ldbStep.1.sup := by -- --- PROOF ---
  set p : Vec ℝ n := fun k => if 0 < Taylm.linCoef T.terms k then -1 else 1
  have hp : p ∈ Taylm.box n := fun k => by simp only [p]; split_ifs <;> norm_num
  have h0 : (0 : Vec ℝ n) ∈ Taylm.box n := fun k => by simp
  have hrp := h p hp
  have hr0 := h 0 h0
  -- `g p` is below the first two estimates, `g 0` below the third
  have hdec := Taylm.polyOf_eq_lin_add_higher T.terms p
  have hb := Taylm.polyBounds_mem (Taylm.higherTerms T.terms) hp
  have hlin : ∑ k, Taylm.linCoef T.terms k * p k ≤ ∑ k, |Taylm.linCoef T.terms k| := by
    refine Finset.sum_le_sum fun k _ => ?_
    have := abs_le.1 (hp k)
    have h1 := le_abs_self (Taylm.linCoef T.terms k * p k)
    rw [abs_mul] at h1
    nlinarith [abs_nonneg (Taylm.linCoef T.terms k), abs_le.2 this]
  have hA : g p ≤ T.constCoef + ∑ k, |Taylm.linCoef T.terms k|
      + ((Taylm.polyBounds (Taylm.higherTerms T.terms)).sup + T.rem.sup) := by
    simp only [Taylm.poly, Taylm.constCoef] at hrp ⊢
    linarith [hrp.2, hb.2]
  have hB : g p ≤ T.poly p + T.rem.sup := by linarith [hrp.2]
  have hC : g 0 ≤ T.poly 0 + T.rem.sup := by linarith [hr0.2]
  -- one of the two points is at most `Min`, so it is kept
  have hex : ∃ q ∈ Taylm.box n, g q ≤ T.ldbStep.1.sup := by
    simp only [Taylm.ldbStep]
    rcases le_total (T.poly 0 + T.rem.sup) (min (T.constCoef + ∑ k, |Taylm.linCoef T.terms k|
      + ((Taylm.polyBounds (Taylm.higherTerms T.terms)).sup + T.rem.sup)) (T.poly p + T.rem.sup))
      with hc | hc
    · exact ⟨0, h0, le_min (le_trans hC (le_trans hc (min_le_left _ _)))
        (le_min (le_trans hC (le_trans hc (min_le_right _ _))) hC)⟩
    · exact ⟨p, hp, le_min hA (le_min hB (le_trans (le_min hA hB) hc))⟩
  obtain ⟨q, hq, hgq⟩ := hex
  refine ⟨q, hq, ?_, hgq⟩
  by_contra hc
  exact absurd (Taylm.ldbStep_reduce h hq hc) (not_lt.2 hgq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
