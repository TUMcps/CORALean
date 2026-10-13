import CORALean.ContSet.Taylm.Real.Operations.GoLowerBound
import CORALean.ContSet.Taylm.Real.Definitions.GoodBox
import CORALean.ContSet.Taylm.Real.Theorems.PolyBoxBoundsMem
import CORALean.ContSet.Taylm.Real.Theorems.ReexpandOuter
import CORALean.ContSet.Taylm.Real.Theorems.ExistsNormalized
import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
import CORALean.ContSet.Taylm.Real.Theorems.LdbLe
import CORALean.ContSet.Taylm.Real.Theorems.QfbLowerLe

/-!
# COSY-GO's bound of a box is a lower bound

Each of the four bounders of [1, Sec. 4] is sound on a sub-box of the normalized box, so their
maximum is.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.goLowerBound_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : ℝ)
    (fuel : ℕ) {B : Fin n → ℝ × ℝ} (hB : Taylm.GoodBox B) {t : Vec ℝ n}
    (ht : Taylm.InBox B t) : T.goLowerBound ε fuel B ≤ f t := by -- --- PROOF ---
  have hB' : ∀ k, -1 ≤ (B k).1 ∧ (B k).1 ≤ (B k).2 ∧ (B k).2 ≤ 1 := fun k =>
    ⟨(hB k).1, le_trans (ht k).1 (ht k).2, (hB k).2.2.2⟩
  have hE := Taylm.reexpand_outer h hB'
  obtain ⟨s, hs, hst⟩ := Taylm.exists_normalized ht
  have htbox : t ∈ Taylm.box n := fun k => abs_le.2
    ⟨le_trans (hB k).1 (ht k).1, le_trans (ht k).2 (hB k).2.2.2⟩
  -- each bounder is sound on its own
  have hIN : (Taylm.polyBoxBounds T.terms B).1 + T.remInf ≤ f t := by
    have := Taylm.polyBoxBounds_mem T.terms ht
    have hr := h t htbox
    simp only [Taylm.poly] at hr
    linarith [hr.1]
  have hTM : (T.reexpand B).bounds.1 ≤ f t := by
    have := (Taylm.bounds_mem hE hs).1; rwa [hst] at this
  have hLDB : (T.reexpand B).ldb ε fuel ≤ f t := by
    have := Taylm.ldb_le hE ε fuel hs; rwa [hst] at this
  have hQFB : (@ite _ (Taylm.hessian (T.reexpand B).terms).PosSemidef (Classical.dec _)
      ((T.reexpand B).qfbLower (Taylm.hessian (T.reexpand B).terms) 0)
      (T.reexpand B).bounds.1) ≤ f t := by
    split_ifs with hH
    · have := Taylm.qfbLower_le hE hH 0 hs; rwa [hst] at this
    · exact hTM
  simp only [Taylm.goLowerBound]
  exact max_le (max_le hIN hTM) (max_le hLDB hQFB)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
