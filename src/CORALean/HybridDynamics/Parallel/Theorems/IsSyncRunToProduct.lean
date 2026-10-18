module

public import CORALean.HybridDynamics.Parallel.Operations.ProductSync
public import CORALean.HybridDynamics.Parallel.Definitions.IsSyncRun
public import CORALean.HybridDynamics.Parallel.Theorems.IsStayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset
public import CORALean.HybridDynamics.Parallel.Theorems.LiftSyncTransitionReset

@[expose] public section

/-!
# Every run with synchronization labels is a run of the labeled product

`IsRun.toProductWith` for `IsSyncRun`, by the run's recursion. A stay is `IsStay.trajectoryWith`
(the labeled product differs from `productWith` in its transitions only, which a trajectory does not
read); an unlabeled jump is the lifted transition, in the merged list's first part; a synchronized
jump is `liftSyncTransition`, in its second, available because every participant has its
transition, its guard met by `SyncLifting.mem_guardAll` and its reset the participants' resets,
by `liftSyncTransition_reset`. For any flow with `FlowLaw`, `mergeFlowsLinearSys` among them.

The soundness direction only. The converse would need the lifted guards and the conjunction to be
exact, and the product's labeled transition to be the only way to take a labeled transition, which
holds here since labeled transitions are not lifted alone, but is not proved.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type} {Λ : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A synchronized parallel run, its states stacked, is a run of the labeled product. -/
theorem ParallelHybridAutomaton.IsSyncRun.toProductSync [ExactScalar 𝕋] [DecidableEq Λ]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.FlowLaw F U W)
    (slift : ParallelHybridAutomaton.SyncLifting S G n m)
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ) {ℓ ℓ' : ∀ i, L i}
    {x y : ∀ i, Vec ℝ (n i)} (run : P.IsSyncRun lab ℓ x ℓ' y) : -- --- STMT ---
    (P.productSync slift lab F U W).IsRun ℓ (stack x) ℓ' (stack y) := by -- --- PROOF ---
  -- a stay of the labeled product's location is one of `productWith`'s: transitions are not read
  have key : ∀ {ℓ : ∀ i, L i} {τ : ℝ} {X : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m},
      P.IsStay ℓ τ X u w g → ∃ g' w', ((P.productSync slift lab F U W).loc ℓ).IsTrajectory τ
        (fun t => stack fun i => X i t) g' w' := fun h => by
    obtain ⟨g', w', h'⟩ := h.trajectoryWith hF slift.toLifting
    exact ⟨g', w', h'.nonneg, h'.input, h'.dist, h'.meas, h'.integrable, h'.cont, h'.flow,
      h'.invariant⟩
  induction run with
  | @flow ℓ₁ τ X u w g h =>
    obtain ⟨g', w', htr⟩ := key h
    exact HybridAutomaton.IsRun.flow (HA := P.productSync slift lab F U W) htr
  | @jump ℓ₁ ℓ₂ τ X u w g Y c e h hmem hlab hguard rest ih =>
    obtain ⟨g', w', htr⟩ := key h
    refine HybridAutomaton.IsRun.jump (HA := P.productSync slift lab F U W)
      (e := ParallelHybridAutomaton.liftTransition slift.toLifting ℓ₁ c e) htr ?_ ?_ ?_
    · -- the lifted transition is in the unlabeled part of the merged list
      refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_finRange _,
        List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨hmem, by simp [hlab]⟩, rfl⟩⟩)
    · exact slift.mem_guard _ _ (fun i => _) hguard
    · rw [ParallelHybridAutomaton.liftTransition_reset]
      exact ih
  | @sync ℓ₁ ℓ₂ τ X u w g Y a ha h havail hguard rest ih =>
    obtain ⟨g', w', htr⟩ := key h
    refine HybridAutomaton.IsRun.jump (HA := P.productSync slift lab F U W)
      (e := P.liftSyncTransition slift lab ℓ₁ a) htr ?_ ?_ ?_
    · -- the synchronized transition is in the second part, all participants being ready
      refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨a, ha, ?_⟩)
      rw [if_pos havail]
    · refine slift.mem_guardAll _ (fun i => X i τ) ?_
      intro c g hg
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hg
      exact hguard c e he
    · rw [ParallelHybridAutomaton.liftSyncTransition_reset]
      exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
