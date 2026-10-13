module

public import CORALean.ContSet.Taylm.Float.Operations.BoundsProd
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# A product of brackets lies in its bracket

If `x` lies in `I` and each `e k` in `E k`, then `x · ∏ e k` lies in `boundsProd E l I`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {ι : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.boundsProd_mem (E : ι → 𝕋 × 𝕋) (e : ι → ℝ) :
    ∀ (l : List ι) (I : 𝕋 × 𝕋) (x : ℝ), toReal I.1 ≤ x → x ≤ toReal I.2 →
      (∀ k ∈ l, toReal (E k).1 ≤ e k ∧ e k ≤ toReal (E k).2) →
      toReal (Taylm.boundsProd E l I).1 ≤ x * (l.map e).prod ∧
        x * (l.map e).prod ≤ toReal (Taylm.boundsProd E l I).2 := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro I x h1 h2 _; simpa using ⟨h1, h2⟩
  | cons k l ih =>
    intro I x h1 h2 hE
    have hk := hE k (List.mem_cons_self ..)
    have hP := Real.Interval.mul_between_corners h1 h2 hk.1 hk.2
    have := ih (Interval.mulLo I.1 I.2 (E k).1 (E k).2, Interval.mulHi I.1 I.2 (E k).1 (E k).2)
      (x * e k) (le_trans (Interval.mulLo_le _ _ _ _) hP.1)
      (le_trans hP.2 (Interval.le_mulHi _ _ _ _)) fun k' hk' => hE k' (List.mem_cons_of_mem _ hk')
    simpa only [Taylm.boundsProd, List.map_cons, List.prod_cons, mul_assoc] using this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
