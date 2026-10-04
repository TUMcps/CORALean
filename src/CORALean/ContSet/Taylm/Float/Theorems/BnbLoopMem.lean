import CORALean.ContSet.Taylm.Float.Operations.BnbLoop
import CORALean.ContSet.Taylm.Float.Operations.Covers
import CORALean.ContSet.Taylm.Float.Theorems.SplitAtCovers
import CORALean.ContSet.Taylm.Float.Theorems.ListMinLe
import CORALean.ContSet.Taylm.Float.Theorems.LeListMax

/-!
# `Taylm.bnbLoop` brackets the function

If every sub-box's bound brackets `g`, the loop's result brackets `g` at each point of the
starting box, whichever way the loop stops: the list always covers the box, the steps only halve
boxes.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bnbLoop_mem {bnd : (Fin n → 𝕋 × 𝕋) → 𝕋 × 𝕋} {g : Vec ℝ n → ℝ}
    (hb : ∀ B t, Taylm.InBox B t → toReal (bnd B).1 ≤ g t ∧ g t ≤ toReal (bnd B).2) (ε : 𝕋)
    {X : Fin n → 𝕋 × 𝕋} {t : Vec ℝ n} (ht : Taylm.InBox X t) :
    ∀ (fuel : ℕ) (l : List (Fin n → 𝕋 × 𝕋)), Taylm.Covers X l →
      toReal (Taylm.bnbLoop bnd ε fuel l).1 ≤ g t ∧
        g t ≤ toReal (Taylm.bnbLoop bnd ε fuel l).2 := by -- --- PROOF ---
  -- the union of a covering list holds the value
  have hunion : ∀ l, Taylm.Covers X l →
      toReal (Taylm.listMin (fun B => (bnd B).1) l) ≤ g t ∧
        g t ≤ toReal (Taylm.listMax (fun B => (bnd B).2) l) := by
    intro l hl
    obtain ⟨B, hB, htB⟩ := hl t ht
    have := hb B t htB
    exact ⟨le_trans (Taylm.listMin_le (fun B => (bnd B).1) hB) this.1,
      le_trans this.2 (Taylm.le_listMax (fun B => (bnd B).2) hB)⟩
  -- a step keeps the cover
  have hstep : ∀ l, Taylm.Covers X l → Taylm.Covers X (Taylm.bnbStep bnd l) := by
    intro l hl
    simp only [Taylm.bnbStep]
    split_ifs
    · exact Taylm.splitAt_covers _ hl
    · exact Taylm.splitAt_covers _ (Taylm.splitAt_covers _ hl)
  intro fuel
  induction fuel with
  | zero => intro l hl; exact hunion l hl
  | succ k ih =>
    intro l hl
    simp only [Taylm.bnbLoop]
    split_ifs
    · exact hunion _ (hstep l hl)
    · exact ih _ (hstep l hl)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
