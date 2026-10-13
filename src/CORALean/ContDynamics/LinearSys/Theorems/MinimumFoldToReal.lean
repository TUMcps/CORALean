import CORALean.ContDynamics.LinearSys.Operations.MinimumFold
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# The float minimum reads as the real one

`minimum` is exact, so the real value of `minimumFold f` is the infimum of the real values.
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

theorem LinearSys.toReal_minimumFold {k : ℕ} (f : Fin (k + 1) → 𝕋) :
    toReal (LinearSys.minimumFold f) =
      Finset.univ.inf' Finset.univ_nonempty fun j => toReal (f j) := by -- --- PROOF ---
  -- the fold is below every entry and equal to one
  have key : ∀ {k : ℕ} (f : Fin (k + 1) → 𝕋),
      (∀ j, toReal (LinearSys.minimumFold f) ≤ toReal (f j)) ∧
      ∃ j, toReal (LinearSys.minimumFold f) = toReal (f j) := by
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
      rw [LinearSys.minimumFold, toReal_minimum]
      refine ⟨fun l => ?_, ?_⟩
      · refine Fin.cases ?_ (fun l' => ?_) l
        · exact min_le_left _ _
        · exact le_trans (min_le_right _ _) (h1 l')
      · rw [hj]
        rcases le_total (toReal (f 0)) (toReal (f j.succ)) with h | h
        · exact ⟨0, min_eq_left h⟩
        · exact ⟨j.succ, min_eq_right h⟩
  -- so the fold is the supremum (infimum) of the real values
  obtain ⟨h1, j, hj⟩ := key f
  refine le_antisymm (Finset.le_inf' _ _ fun l _ => h1 l) ?_
  rw [hj]
  exact Finset.inf'_le (fun l => toReal (f l)) (Finset.mem_univ j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
