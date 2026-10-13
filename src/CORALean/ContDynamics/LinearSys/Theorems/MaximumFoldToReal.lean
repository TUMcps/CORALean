module

public import CORALean.ContDynamics.LinearSys.Operations.MaximumFold
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The float maximum reads as the real one

`maximum` is exact, so the real value of `maximumFold f` is the supremum of the real values.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.toReal_maximumFold {k : ℕ} (f : Fin (k + 1) → 𝕋) :
    toReal (LinearSys.maximumFold f) =
      Finset.univ.sup' Finset.univ_nonempty fun j => toReal (f j) := by -- --- PROOF ---
  -- the fold is above every entry and equal to one
  have key : ∀ {k : ℕ} (f : Fin (k + 1) → 𝕋),
      (∀ j, toReal (f j) ≤ toReal (LinearSys.maximumFold f)) ∧
      ∃ j, toReal (LinearSys.maximumFold f) = toReal (f j) := by
    intro k
    induction k with
    | zero =>
      intro f
      exact ⟨fun j => by
        have hj0 : j = 0 := Fin.ext (by have := j.isLt; omega)
        rw [hj0]
        exact le_rfl, 0, rfl⟩
    | succ k ih =>
      intro f
      -- the head against the fold of the tail
      obtain ⟨h1, j, hj⟩ := ih fun i => f i.succ
      rw [LinearSys.maximumFold, toReal_maximum]
      refine ⟨fun l => ?_, ?_⟩
      · refine Fin.cases ?_ (fun l' => ?_) l
        · exact le_max_left _ _
        · exact le_trans (h1 l') (le_max_right _ _)
      · rw [hj]
        rcases le_total (toReal (f 0)) (toReal (f j.succ)) with h | h
        · exact ⟨j.succ, max_eq_right h⟩
        · exact ⟨0, max_eq_left h⟩
  -- so the fold is the supremum (infimum) of the real values
  obtain ⟨h1, j, hj⟩ := key f
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun l _ => h1 l)
  rw [hj]
  exact Finset.le_sup' (fun l => toReal (f l)) (Finset.mem_univ j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
