module

public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Definitions.Box

@[expose] public section

/-!
# A point of a box in normalized coordinates

`t = mid + rad ⊙ s` for some `s` in the normalized box, `sₖ = 0` along a direction of radius
zero: how a statement about a re-expanded model reaches the box's points.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.exists_normalized {B : Fin n → ℝ × ℝ} {t : Vec ℝ n} (ht : Taylm.InBox B t) :
    ∃ s ∈ Taylm.box n,
      (fun k => Taylm.boxMid B k + Taylm.boxRad B k * s k) = t := by -- --- PROOF ---
  refine ⟨fun k => if Taylm.boxRad B k = 0 then 0 else (t k - Taylm.boxMid B k) / Taylm.boxRad B k,
    fun k => ?_, funext fun k => ?_⟩
  · simp only
    split_ifs with hr
    · simp
    · have := ht k
      have hr0 : 0 < Taylm.boxRad B k := lt_of_le_of_ne
        (by simp only [Taylm.boxRad]; linarith [this.1, this.2]) (Ne.symm hr)
      rw [abs_div, abs_of_pos hr0, div_le_one hr0, abs_le]
      simp only [Taylm.boxRad, Taylm.boxMid] at hr0 ⊢
      constructor <;> linarith [this.1, this.2]
  · simp only
    split_ifs with hr
    · have := ht k
      simp only [Taylm.boxRad, Taylm.boxMid] at hr ⊢
      linarith [this.1, this.2]
    · field_simp
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
