module

public import CORALean.ContSet.LevelSet.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.LevelSet.Real.Theorems.RepresentsaEmptySetSound

@[expose] public section

/-!
# A `true` from `LevelSet.representsa_emptySet` proves the set empty

Every row's certified comparison, read as reals, is the real test at the bounds read as reals
(and cast to `EReal`), and `CORALean.Real.LevelSet.representsa_emptySet_sound` concludes. The
bounds are assumed to enclose each row's range, as over ℝ.
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

theorem LevelSet.representsa_emptySet_sound (L : CORALean.Real.LevelSet n)
    (O : Fin L.m → Interval 𝕋)
    (hO : ∀ i x, toReal (O i).inf ≤ L.f x i ∧ L.f x i ≤ toReal (O i).sup)
    (hm : 0 < L.m) (h : LevelSet.representsa_emptySet L O = true) :
    L.construct = ∅ := by -- --- PROOF ---
  refine CORALean.Real.LevelSet.representsa_emptySet_sound L
    (fun i => ⟨((toReal (O i).inf : ℝ) : EReal), ((toReal (O i).sup : ℝ) : EReal)⟩)
    (fun i x => ⟨EReal.coe_le_coe_iff.mpr (hO i x).1, EReal.coe_le_coe_iff.mpr (hO i x).2⟩)
    hm ?_
  -- each row's certified comparison, read as reals
  simp only [LevelSet.representsa_emptySet, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  intro i
  have hi := h i
  rcases hop : L.op i with _ | _ | _ <;> rw [hop] at hi <;> simp only
  · -- `≤`
    have hlt := toReal_lt_of_ltStrict hi
    rw [toReal_zero] at hlt
    exact not_le.mpr (by exact_mod_cast hlt)
  · -- `<`
    have hle := toReal_le_of_le hi
    rw [toReal_zero] at hle
    exact not_lt.mpr (by exact_mod_cast hle)
  · simp only [Bool.or_eq_true] at hi
    rintro ⟨h₁, h₂⟩
    rcases hi with hi | hi
    · have hlt := toReal_lt_of_ltStrict hi
      rw [toReal_zero] at hlt
      have : toReal (O i).inf ≤ 0 := by exact_mod_cast h₁
      linarith
    · have hlt := toReal_lt_of_ltStrict hi
      rw [toReal_zero] at hlt
      have : 0 ≤ toReal (O i).sup := by exact_mod_cast h₂
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
