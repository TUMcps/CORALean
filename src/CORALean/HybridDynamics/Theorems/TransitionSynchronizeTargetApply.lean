module

public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTarget

@[expose] public section

/-!
# `Transition.synchronizeTarget` moves each component

With `compIdx` injective, the target tuple has the target of transition `i` at `compIdx i`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k q : ℕ} {L : Fin k → Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold over a duplicate-free list of transitions: the listed ones are moved. -/
theorem aux_synchronizeTarget_fold (compIdx : Fin q → Fin k) (target : ∀ i, L (compIdx i))
    (hinj : Function.Injective compIdx) (l : List (Fin q)) (hl : l.Nodup) (t₀ : ∀ c, L c)
    (i : Fin q) : -- --- STMT ---
    (l.foldl (fun t j => Function.update t (compIdx j) (target j)) t₀) (compIdx i) =
      if i ∈ l then target i else t₀ (compIdx i) := by -- --- PROOF ---
  induction l generalizing t₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih (List.nodup_cons.mp hl).2]
    by_cases hia : i = a
    · subst hia
      have : i ∉ l := (List.nodup_cons.mp hl).1
      simp [this]
    · have hne : compIdx a ≠ compIdx i := fun h => hia (hinj h).symm
      simp [hia, Function.update_of_ne hne.symm]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `compIdx` injective, each participating component moves to its own transition's
target. -/
theorem Transition.synchronizeTarget_apply (locID : ∀ c, L c) (compIdx : Fin q → Fin k)
    (target : ∀ i, L (compIdx i)) (hinj : Function.Injective compIdx) (i : Fin q) :
    Transition.synchronizeTarget locID compIdx target (compIdx i) = target i := by
  unfold Transition.synchronizeTarget
  rw [aux_synchronizeTarget_fold compIdx target hinj _ (List.nodup_finRange q)]
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
