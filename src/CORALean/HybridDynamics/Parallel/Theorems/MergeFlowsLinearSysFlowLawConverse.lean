module

public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlow
public import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Definitions.IsFlowLawConverse
public import CORALean.HybridDynamics.Parallel.Definitions.IsFeedthroughFree
public import CORALean.HybridDynamics.Parallel.Definitions.GlobalsDistinct
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeDistSets

@[expose] public section

/-!
# The product's flow has the converse flow law

At `ℝ`, `mergeFlowsLinearSys` with `mergeInputSets` and `mergeDistSets` has `IsFlowLawConverse`
under `IsFeedthroughFree`, `GlobalsDistinct`, an exact `Lifting` and nonempty input sets. For an
input `g` of the product in `mergeInputSets` and a disturbance in `mergeDistSets`, the components'
global inputs are `g` and their disturbances the blocks (`Lifting.IsExact`); an input bound to an
output is that output, computed with the feeding component's output-bound inputs at `0`, which
`IsFeedthroughFree` makes no difference; `mergeFlowsLinearSys_flow` is the coordinate identity.

## Inputs
* `P` – parallel automaton
* `lift` – lifting

## Hypotheses
* `hfeed` – no feedthrough between bound outputs
* `hdist` – no global input feeds two inputs
* `hne` – every input set is nonempty
* `hex` – lifting is exact

## Conclusion
* the merged flow has the converse flow law
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- `bindsAt` binds to a global input exactly where `binds` does. -/
private theorem aux_bindsAt_global {𝕋 : Type} {P : ParallelHybridAutomaton S G k L 𝕋 n m}
    {ℓ : ∀ i, L i} {i : Fin k} {j : Fin (P.sys ℓ i).m} {a : Fin m}
    (h : P.bindsAt ℓ i j = .global a) : -- --- CONCL ---
    P.binds i (Fin.cast (P.inputs_eq i (ℓ i)) j) = .global a := by -- --- PROOF ---
  unfold ParallelHybridAutomaton.bindsAt at h
  split at h
  · rename_i a' h'
    cases h
    exact h'
  · cases h

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- `GlobalsDistinct` at the dimensions of the locations `ℓ`. -/
private theorem aux_bindsAt_distinct {𝕋 : Type} {P : ParallelHybridAutomaton S G k L 𝕋 n m}
    (hdist : P.GlobalsDistinct) (ℓ : ∀ i, L i) : -- --- CONCL ---
    ∀ i i' j j' a, P.bindsAt ℓ i j = .global a → P.bindsAt ℓ i' j' = .global a →
      (⟨i, j⟩ : Σ i, Fin (P.sys ℓ i).m) = ⟨i', j'⟩ := by -- --- PROOF ---
  intro i i' j j' a h h'
  have he := hdist _ _ _ _ a (aux_bindsAt_global h) (aux_bindsAt_global h')
  obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.mp he
  -- the same component, and the cast inputs agree, so the inputs do
  have : j = j' := Fin.ext (by simpa using congrArg Fin.val (eq_of_heq hj))
  rw [this]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.mergeFlowsLinearSys_isFlowLawConverse
    {P : ParallelHybridAutomaton S G k L ℝ n m} (hfeed : P.IsFeedthroughFree)
    (hdist : P.GlobalsDistinct)
    (hne : ∀ (ℓ : ∀ i, L i) i, (construct ((P.comp i).loc (ℓ i)).U).Nonempty)
    {lift : ParallelHybridAutomaton.Lifting S G n m} (hex : lift.IsExact) : -- --- CONCL ---
    P.IsFlowLawConverse (fun ℓ => mergeFlowsLinearSys (P.sys ℓ) (P.bindsAt ℓ))
      (P.mergeInputSets lift) (P.mergeDistSets lift) := by -- --- PROOF ---
  classical
  intro ℓ x g w' hg hw
  -- the inputs: a global one is `g`, an output-bound one the output, its own bound inputs at `0`
  set u₀ : ∀ i, Vec ℝ (P.sys ℓ i).m := fun i j => match P.bindsAt ℓ i j with
    | .global a => g a
    | .output _ _ => 0 with hu₀
  set u : ∀ i, Vec ℝ (P.sys ℓ i).m := fun i j => match P.bindsAt ℓ i j with
    | .global a => g a
    | .output c s => ((P.sys ℓ c).C *ᵥ x c + (P.sys ℓ c).D *ᵥ u₀ c + (P.sys ℓ c).k) s with hu
  -- a feeding output does not see the difference: `D` is zero at the output-bound inputs
  have hD : ∀ i j c s, P.bindsAt ℓ i j = .output c s →
      ((P.sys ℓ c).D *ᵥ u c) s = ((P.sys ℓ c).D *ᵥ u₀ c) s := by
    intro i j c s h
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [hu, hu₀]
    cases h' : P.bindsAt ℓ c j' with
    | global a => rfl
    | output c' s' => simp [show (P.sys ℓ c).D s j' = 0 from hfeed ℓ i j c s h j' c' s' h']
  -- so the inputs obey the bindings, the feeding outputs read at the inputs themselves
  have hbound : ∀ i j, u i j = match P.bindsAt ℓ i j with
      | .global a => g a
      | .output c s => ((P.sys ℓ c).C *ᵥ x c + (P.sys ℓ c).D *ᵥ u c + (P.sys ℓ c).k) s := by
    intro i j
    cases h : P.bindsAt ℓ i j with
    | global a =>
      show u i j = g a
      simp only [hu, h]
    | output c s =>
      -- `D u` is `D u₀` here, which is how `u` was built
      show u i j = ((P.sys ℓ c).C *ᵥ x c + (P.sys ℓ c).D *ᵥ u c + (P.sys ℓ c).k) s
      rw [Pi.add_apply, Pi.add_apply, hD i j c s h]
      simp only [hu, h, Pi.add_apply]
  refine ⟨u, unstack w', g, fun i j => ?_, hex.input_inv _ (aux_bindsAt_distinct hdist ℓ) _
    (hne ℓ) g hg, hex.dist_inv _ _ (by rwa [stack_unstack]), fun i a => ?_⟩
  · -- the binding, as `boundInput` reads it
    rw [hbound i j]
    unfold ParallelHybridAutomaton.boundInput
    cases P.bindsAt ℓ i j <;> simp
  · -- the merged equation, its bound inputs those of the components
    have := mergeFlowsLinearSys_flow (P.sys ℓ) (P.bindsAt ℓ)
      (fun i j c s h j' c' s' h' => hfeed ℓ i j c s h j' c' s' h') x g (unstack w') u
      (fun i j => by
        rw [hbound i j]
        cases P.bindsAt ℓ i j <;> rfl) i a
    rw [stack_unstack] at this
    simpa only [Pi.add_apply, Scalar.toRealMat_real, Scalar.toRealVec_real] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
