module

public import CORALean.ContSet.LevelSet.Float.Operations.RepresentsaFullspace
public import CORALean.ContSet.LevelSet.Real.Theorems.RepresentsaFullspaceSound

@[expose] public section

/-!
# A `true` from `LevelSet.representsa_fullspace` proves the set is everything

Every row's certified comparison, read as reals, is the real test at the bounds read as reals
(and cast to `EReal`), and `CORALean.Real.LevelSet.representsa_fullspace_sound` concludes. The
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

theorem LevelSet.representsa_fullspace_sound (L : CORALean.Real.LevelSet n)
    (O : Fin L.m → Interval 𝕋)
    (hO : ∀ i x, toReal (O i).inf ≤ L.f x i ∧ L.f x i ≤ toReal (O i).sup)
    (h : LevelSet.representsa_fullspace L O = true) :
    L.construct = Set.univ := by -- --- PROOF ---
  refine CORALean.Real.LevelSet.representsa_fullspace_sound L
    (fun i => ⟨((toReal (O i).inf : ℝ) : EReal), ((toReal (O i).sup : ℝ) : EReal)⟩)
    (fun i x => ⟨EReal.coe_le_coe_iff.mpr (hO i x).1, EReal.coe_le_coe_iff.mpr (hO i x).2⟩) ?_
  -- each row's certified comparison, read as reals
  simp only [LevelSet.representsa_fullspace, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  intro i
  have hi := h i
  rcases hop : L.op i with _ | _ | _ <;> rw [hop] at hi <;> simp only
  · -- `≤`
    have hle := toReal_le_of_le hi
    rw [toReal_zero] at hle
    exact not_lt.mpr (by exact_mod_cast hle)
  · -- `<`
    have hlt := toReal_lt_of_ltStrict hi
    rw [toReal_zero] at hlt
    exact not_le.mpr (by exact_mod_cast hlt)
  · simp only [Bool.and_eq_true] at hi
    obtain ⟨⟨a₁, a₂⟩, b₁, b₂⟩ := hi
    have e₁ : toReal (O i).inf = 0 :=
      le_antisymm ((toReal_le_of_le a₁).trans_eq toReal_zero)
        (toReal_zero.symm.trans_le (toReal_le_of_le a₂))
    have e₂ : toReal (O i).sup = 0 :=
      le_antisymm ((toReal_le_of_le b₁).trans_eq toReal_zero)
        (toReal_zero.symm.trans_le (toReal_le_of_le b₂))
    simp [e₁, e₂]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
