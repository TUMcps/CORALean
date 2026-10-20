module

public import CORALean.ContSet.Taylm.Real.Operations.OptBnbAdv
public import CORALean.ContSet.Taylm.Real.Theorems.BranchAndBoundMem
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Taylm.optBnbAdv` bounds the enclosed function

On the normalized box the polynomial lies in the branch and bound interval, [1, Alg. 1], and the
function differs from it by the remainder.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `ε` – tolerance
* `fuel` – step budget
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `ht` – point lies in the unit box

## Conclusion
* the advanced branch and bound enclosure contains the function's value

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optBnbAdv_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : ℝ) (fuel : ℕ)
    {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    (T.optBnbAdv ε fuel).inf ≤ f t ∧ f t ≤ (T.optBnbAdv ε fuel).sup := by -- --- PROOF ---
  have hb := Taylm.branchAndBound_mem T.terms (fun _ => ⟨-1, 1⟩) ε true fuel (t := t)
    fun k => abs_le.1 (ht k)
  have hr := h t ht
  simp only [Taylm.poly] at hr
  simp only [Taylm.optBnbAdv]
  constructor <;> linarith [hb.1, hb.2, hr.1, hr.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
