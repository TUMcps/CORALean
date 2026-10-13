import CORALean.NN.Layers.Operations.AllOver

/-!
# A passed conjunction passes at every index

By induction on the length, the head and then the tail.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem allOver_apply : ∀ {k : ℕ} (f : Fin k → Bool),
    allOver f = true → ∀ i, f i = true := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ _ i => absurd i.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    intro f h i
    rw [allOver, Bool.and_eq_true] at h
    exact Fin.cases h.1 (fun j => ih (fun i' => f i'.succ) h.2 j) i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
