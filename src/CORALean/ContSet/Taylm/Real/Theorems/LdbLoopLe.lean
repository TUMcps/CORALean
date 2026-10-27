module

public import CORALean.ContSet.Taylm.Real.Operations.LdbLoop
public import CORALean.ContSet.Taylm.Real.Theorems.LdbStepLower
public import CORALean.ContSet.Taylm.Real.Theorems.LdbStepReduce
public import CORALean.ContSet.Taylm.Real.Theorems.LdbStepWitness
public import CORALean.ContSet.Taylm.Real.Theorems.LdbStepSub
public import CORALean.ContSet.Taylm.Real.Theorems.ExistsNormalized
public import CORALean.ContSet.Taylm.Real.Theorems.ReexpandOuter

@[expose] public section

/-!
# The LDB iteration bounds the minimum

[1, Sec. 2]: `M` is a lower bound of the minimum on every box the iteration passes through. On the
last box by `ldbStep_lower`; a point cut off earlier is above that step's `Min`, which a kept
point is below, and the kept point is in the next box, where the induction holds.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `ε` – tolerance

## Hypotheses
* `h` – the model encloses the function

## Conclusion
* the iteration's bound is at most the function's value on every box in the unit box

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

theorem Taylm.ldbLoop_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (ε : ℝ) : -- --- CONCL ---
    ∀ (fuel : ℕ) (B : Fin n → Interval ℝ), (∀ k, -1 ≤ (B k).inf ∧ (B k).sup ≤ 1) →
      ∀ t, Taylm.IsInBox B t → Taylm.ldbLoop T ε fuel B ≤ f t := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero =>
    intro B hB t ht
    obtain ⟨s, hs, rfl⟩ := Taylm.exists_normalized ht
    have hB' : ∀ k, -1 ≤ (B k).inf ∧ (B k).inf ≤ (B k).sup ∧ (B k).sup ≤ 1 := fun k =>
      ⟨(hB k).1, le_trans (ht k).1 (ht k).2, (hB k).2⟩
    exact Taylm.ldbStep_lower (Taylm.reexpand_outer h hB') hs
  | succ fuel ih =>
    intro B hB t ht
    have hB' : ∀ k, -1 ≤ (B k).inf ∧ (B k).inf ≤ (B k).sup ∧ (B k).sup ≤ 1 := fun k =>
      ⟨(hB k).1, le_trans (ht k).1 (ht k).2, (hB k).2⟩
    have hE := Taylm.reexpand_outer h hB'
    obtain ⟨s, hs, rfl⟩ := Taylm.exists_normalized ht
    simp only [Taylm.ldbLoop]
    split_ifs with hd
    · set R := (T.reexpand B).ldbStep.2
      -- the kept box lies in the current one
      have hrad : ∀ k, 0 ≤ Taylm.boxRad B k := fun k => by
        simp only [Taylm.boxRad]; linarith [(hB' k).2.1]
      have hsub : ∀ k, -1 ≤ Taylm.boxMid B k + Taylm.boxRad B k * (R k).inf ∧
          Taylm.boxMid B k + Taylm.boxRad B k * (R k).sup ≤ 1 := by
        intro k
        have hR := Taylm.ldbStep_sub (T.reexpand B) k
        have := hrad k
        simp only [Taylm.boxMid, Taylm.boxRad] at this ⊢
        constructor <;> nlinarith [(hB' k).1, (hB' k).2.1, (hB' k).2.2, hR.1, hR.2]
      have himg : ∀ q, Taylm.IsInBox R q → Taylm.IsInBox (fun k =>
          ⟨Taylm.boxMid B k + Taylm.boxRad B k * (R k).inf,
            Taylm.boxMid B k + Taylm.boxRad B k * (R k).sup⟩)
          (fun k => Taylm.boxMid B k + Taylm.boxRad B k * q k) := by
        intro q hq k
        exact ⟨by nlinarith [(hq k).1, hrad k], by nlinarith [(hq k).2, hrad k]⟩
      by_cases hin : Taylm.IsInBox R s
      · exact ih _ hsub _ (himg s hin)
      · -- the point was cut: a kept point is lower still
        have hlt := Taylm.ldbStep_reduce hE hs hin
        obtain ⟨q, hq, hqR, hgq⟩ := Taylm.ldbStep_witness hE
        have := ih _ hsub _ (himg q hqR)
        linarith
    · exact Taylm.ldbStep_lower hE hs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
