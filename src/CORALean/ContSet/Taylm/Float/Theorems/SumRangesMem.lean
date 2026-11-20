module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `Taylm.sumRanges` holds the sum

## Inputs
* `α` – type of the elements
* `f` – interval of each element
* `L` – elements
* `v` – value of each element
* `I` – start interval
* `x` – value in the start interval

## Hypotheses
* `hI` – `x` lies in the start interval
* `hL` – the value of every element lies in its interval

## Conclusion
* `x` plus the sum of the values lies in the sum of the intervals
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sumRanges_mem {α : Type} (f : α → Interval 𝕋) (L : List α) (v : α → ℝ)
    {I : Interval 𝕋} {x : ℝ} (hI : toReal I.inf ≤ x ∧ x ≤ toReal I.sup)
    (hL : ∀ a ∈ L, toReal (f a).inf ≤ v a ∧ v a ≤ toReal (f a).sup) : -- --- CONCL ---
    toReal (Taylm.sumRanges f I L).inf ≤ x + (L.map v).sum ∧
      x + (L.map v).sum ≤ toReal (Taylm.sumRanges f I L).sup := by -- --- PROOF ---
  induction L generalizing I x with
  | nil => simpa [Taylm.sumRanges] using hI
  | cons a L ih =>
    have ha := hL a List.mem_cons_self
    have h₁ := addDown_le_add I.inf (f a).inf
    have h₂ := add_le_addUp I.sup (f a).sup
    -- the first interval joins the start, its value joins `x`
    have := ih (I := ⟨addDown I.inf (f a).inf, addUp I.sup (f a).sup⟩) (x := x + v a)
      ⟨by simp only; linarith [hI.1, ha.1], by simp only; linarith [hI.2, ha.2]⟩
      (fun b hb => hL b (List.mem_cons_of_mem a hb))
    simp only [Taylm.sumRanges, List.foldl_cons, List.map_cons, List.sum_cons] at this ⊢
    constructor <;> linarith [this.1, this.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
