import CORALean.ContDynamics.NonlinearARX.Operations.API

/-!
# One step of the converted system

The window `stack p y (k+1)` is `f` of the window `stack p y k` and the input signal
`feed p u k`: a shift row reads the next block, the last row is the ARX recursion at
`k + p`, its past windows reindexed by `Fin.rev`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The past outputs at `k + p` are the window at `k`, blocks reversed. -/
theorem NonlinearARX.aux_pastOut_rev (y : ℕ → Vec ℝ dy) (k : ℕ) :
    NonlinearARX.pastOut p y (k + p) = fun s => NonlinearARX.stack p y k
      (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2)) := by
  funext s
  simp only [NonlinearARX.pastOut, NonlinearARX.stack, Equiv.symm_apply_apply, Fin.val_rev]
  congr 1; omega

/-- The inputs at `k + p` are the input signal at `k`, blocks reversed. -/
theorem NonlinearARX.aux_pastIn_rev (u : ℕ → Vec ℝ du) (k : ℕ) :
    NonlinearARX.pastIn p u (k + p) = fun s => NonlinearARX.feed p u k
      (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2)) := by
  funext s
  simp only [NonlinearARX.pastIn, NonlinearARX.feed, Equiv.symm_apply_apply, Fin.val_rev]
  congr 1; omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.toNonlinearSysDT_step (sys : NonlinearARX dy du p) {y : ℕ → Vec ℝ dy}
    {u : ℕ → Vec ℝ du}
    (hy : ∀ k, p ≤ k → y k = sys.f (NonlinearARX.pastOut p y k) (NonlinearARX.pastIn p u k))
    (k : ℕ) :
    NonlinearARX.stack p y (k + 1)
      = sys.toNonlinearSysDT.f (NonlinearARX.stack p y k)
        (NonlinearARX.feed p u k) := by -- --- PROOF ---
  funext r
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective r
  simp only [NonlinearARX.stack, NonlinearARX.toNonlinearSysDT, Equiv.symm_apply_apply]
  -- a shift row, or the last row
  by_cases h1 : a.val + 1 < p
  · simp only [dif_pos h1]
    congr 1; omega
  · -- the last row: the recursion at `k + p`, its windows reindexed by `Fin.rev`
    have h2 : a.val + 1 = p := by omega
    have e : k + 1 + a.val = k + p := by omega
    simp only [dif_neg h1]
    rw [e, hy (k + p) (by omega)]
    rw [NonlinearARX.aux_pastOut_rev y k, NonlinearARX.aux_pastIn_rev u k]
    simp only [NonlinearARX.stack, Equiv.symm_apply_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
