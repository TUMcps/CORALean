module

public import CORALean.ContSet.Taylm.Real.Operations.Reexpand
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfReexpTerms
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Taylm.reexpand` encloses the function on the sub-box

The re-expanded polynomial at `s` is the original at `mid + rad ⊙ s` exactly
(`polyOf_reexpTerms`), and for `s` in the normalized box that point lies in the sub-box, hence in
the normalized box, where the original remainder holds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.reexpand_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {B : Fin n → Interval ℝ} (hB : ∀ k, -1 ≤ (B k).inf ∧ (B k).inf ≤ (B k).sup ∧ (B k).sup ≤ 1) :
    (T.reexpand B).Encloses fun s =>
      f fun k => Taylm.boxMid B k + Taylm.boxRad B k * s k := by -- --- PROOF ---
  intro s hs
  -- the point the sub-box's coordinates name lies in the normalized box
  have hin : (fun k => Taylm.boxMid B k + Taylm.boxRad B k * s k) ∈ Taylm.box n := by
    intro k
    have hk := abs_le.1 (hs k)
    have hr : 0 ≤ Taylm.boxRad B k := by simp only [Taylm.boxRad]; linarith [(hB k).2.1]
    rw [abs_le]
    simp only [Taylm.boxMid, Taylm.boxRad] at hr ⊢
    constructor <;> nlinarith [(hB k).1, (hB k).2.1, (hB k).2.2]
  have := h _ hin
  simp only [Taylm.reexpand, Taylm.poly, Taylm.polyOf_reexpTerms]
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
