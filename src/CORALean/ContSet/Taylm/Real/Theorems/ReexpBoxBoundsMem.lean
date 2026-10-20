module

public import CORALean.ContSet.Taylm.Real.Definitions.Box
public import CORALean.ContSet.Taylm.Real.Operations.ReexpBoxBounds
public import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfReexpTerms
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Re-expanded bounds enclose a polynomial over a box

A point `t` of the box is `mid + rad ⊙ s` for `s` in the normalized box (`s = 0` along a
coordinate of radius zero), so `P t` is the re-expanded polynomial at `s` and lies in its bounds.

## Inputs
* `P` – terms of the polynomial
* `B` – box
* `t` – point

## Hypotheses
* `ht` – point lies in the box

## Conclusion
* the polynomial's value lies in the re-expanded bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.reexpBoxBounds_mem (P : List (ℝ × (Fin n → ℕ))) {B : Fin n → Interval ℝ}
    {t : Vec ℝ n} (ht : Taylm.InBox B t) :
    (Taylm.reexpBoxBounds P B).inf ≤ Taylm.polyOf P t ∧
      Taylm.polyOf P t ≤ (Taylm.reexpBoxBounds P B).sup := by -- --- PROOF ---
  -- the normalized coordinates of `t`
  set s : Vec ℝ n := fun k =>
    if Taylm.boxRad B k = 0 then 0 else (t k - Taylm.boxMid B k) / Taylm.boxRad B k
  have hts : (fun k => Taylm.boxMid B k + Taylm.boxRad B k * s k) = t := by
    funext k
    simp only [s]
    split_ifs with hr
    · have := ht k
      simp only [Taylm.boxRad, Taylm.boxMid] at hr ⊢
      linarith [this.1, this.2]
    · field_simp
      ring
  -- and they lie in the normalized box
  have hs : s ∈ Taylm.box n := by
    intro k
    simp only [s]
    split_ifs with hr
    · simp
    · have := ht k
      have hr0 : 0 < Taylm.boxRad B k := lt_of_le_of_ne
        (by simp only [Taylm.boxRad]; linarith [this.1, this.2]) (Ne.symm hr)
      rw [abs_div, abs_of_pos hr0, div_le_one hr0, abs_le]
      simp only [Taylm.boxRad, Taylm.boxMid] at hr0 ⊢
      constructor <;> linarith [this.1, this.2]
  have := Taylm.polyBounds_mem (Taylm.reexpTerms (Taylm.boxMid B) (Taylm.boxRad B) P) hs
  rw [Taylm.polyOf_reexpTerms, hts] at this
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
