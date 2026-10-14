module

public import CORALean.ContSet.LevelSet.Float.Operations.ContainsPoint

@[expose] public section

/-!
# A `true` from `LevelSet.containsPoint` proves membership

Each row's value lies between its bounds, and the certified comparison of the bounds with `0`,
read as reals, places the value on the side its operator asks for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.containsPoint_sound (L : CORALean.Real.LevelSet n) (B : Fin L.m → Interval 𝕋)
    (x : Vec ℝ n) (hB : ∀ i, toReal (B i).inf ≤ L.f x i ∧ L.f x i ≤ toReal (B i).sup)
    (h : LevelSet.containsPoint L B = true) : x ∈ L.construct := by -- --- PROOF ---
  simp only [LevelSet.containsPoint, List.all_eq_true, List.mem_finRange, forall_const] at h
  intro i
  have hi := h i
  have hb := hB i
  rcases hop : L.op i with _ | _ | _ <;> rw [hop] at hi <;>
    simp only [CORALean.Real.CompOp.holds]
  · -- `≤`: the upper bound is at most `0`
    exact le_trans hb.2 ((toReal_le_of_le hi).trans_eq toReal_zero)
  · -- `<`: the upper bound is below `0`
    exact lt_of_le_of_lt hb.2 ((toReal_lt_of_ltStrict hi).trans_eq toReal_zero)
  · -- `=`: both bounds are `0`
    simp only [Bool.and_eq_true] at hi
    obtain ⟨⟨a₁, a₂⟩, b₁, b₂⟩ := hi
    have e₁ : toReal (B i).inf = 0 :=
      le_antisymm ((toReal_le_of_le a₁).trans_eq toReal_zero)
        (toReal_zero.symm.trans_le (toReal_le_of_le a₂))
    have e₂ : toReal (B i).sup = 0 :=
      le_antisymm ((toReal_le_of_le b₁).trans_eq toReal_zero)
        (toReal_zero.symm.trans_le (toReal_le_of_le b₂))
    rw [e₁, e₂] at hb
    exact le_antisymm hb.2 hb.1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
