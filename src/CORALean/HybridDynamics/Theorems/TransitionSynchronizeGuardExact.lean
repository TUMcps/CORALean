module

public import CORALean.HybridDynamics.Operations.TransitionSynchronizeGuard

@[expose] public section

/-!
# `Transition.synchronizeGuard` is the intersection

The synchronized guard denotes the intersection of the guards, with equality: stacking the rows
loses nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q k : ℕ} {L : Fin k → Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The accumulator of the guard fold is the intersection so far. -/
theorem aux_synchronizeGuard_fold (g : Fin q → HPolytope 𝕋 (Vec 𝕋 n)) (l : List (Fin q))
    (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    (l.foldl (fun guard i => HPolytope.intersection guard (g i)) P).construct =
      P.construct ∩ ⋂ i ∈ l, (g i).construct := by -- --- PROOF ---
  induction l generalizing P with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, ← HPolytope.intersection_exact]
    ext x; simp [and_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The synchronized guard denotes the intersection of the guards: exact. -/
theorem Transition.synchronizeGuard_exact (g : Fin q → HPolytope 𝕋 (Vec 𝕋 n)) :
    (Transition.synchronizeGuard g).construct = ⋂ i, (g i).construct := by -- --- PROOF ---
  unfold Transition.synchronizeGuard
  rw [aux_synchronizeGuard_fold]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, List.mem_finRange, forall_true_left]
  exact ⟨fun h => h.2, fun h => ⟨HPolytope.mem_fullspace x, h⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
